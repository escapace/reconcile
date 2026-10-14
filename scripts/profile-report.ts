import { BATCH_SIZE } from '../perf/config'
import type { attribute } from './profile-attribution'
import type { parseDeopts } from './profile-deopts'
import type { AllocAggregate, FrameAggregate } from './profile-frames'

export interface ScenarioResult {
  allocFrames: Map<string, AllocAggregate>
  cpuAttribution: ReturnType<typeof attribute>
  cpuprofilePath: string
  deoptCoverage: ReturnType<typeof parseDeopts>['coverage']
  deopts: ReturnType<typeof parseDeopts>['entries']
  frames: Map<string, FrameAggregate>
  gcTimeUs: number
  heapAttribution: ReturnType<typeof attribute>
  heapprofilePath: string
  scenario: string
  totalTime: number
  traceLogPath: string
}

type DeoptEntry = ScenarioResult['deopts'][number]

interface MeasurementDeopts {
  counts: Map<string, number>
  reasons: Map<string, string[]>
}

interface MergedFrame {
  allocBytesPerOp: number
  functionName: string
  location: string
  selfTimePerOpUs: number
}

function addDeopt({ counts, reasons }: MeasurementDeopts, entry: DeoptEntry): void {
  counts.set(entry.functionName, (counts.get(entry.functionName) ?? 0) + entry.count)
  const known = reasons.get(entry.functionName) ?? []

  if (!known.includes(entry.reason)) {
    known.push(entry.reason)
    reasons.set(entry.functionName, known)
  }
}

/** Deopt counts and distinct reasons per function, from measurement-phase events only. */
function measurementDeopts(deopts: readonly DeoptEntry[]): MeasurementDeopts {
  const result: MeasurementDeopts = { counts: new Map(), reasons: new Map() }
  for (const entry of deopts) if (entry.phase === 'measurement') addDeopt(result, entry)
  return result
}

function scoreFrame(
  frame: MergedFrame,
  deopts: MeasurementDeopts,
  maxAlloc: number,
  maxDeopt: number,
) {
  const deoptCount = deopts.counts.get(frame.functionName) ?? 0
  const reasons = deopts.reasons.get(frame.functionName) ?? []
  const allocPenalty = 0.5 * (frame.allocBytesPerOp / maxAlloc)
  const deoptPenalty = 0.5 * (deoptCount / maxDeopt)
  const score = frame.selfTimePerOpUs * (1 + allocPenalty + deoptPenalty)

  return {
    allocBytesPerOp: frame.allocBytesPerOp,
    deoptSignals: deoptCount > 0 ? `${deoptCount}× deopt (${reasons.join(', ')})` : 'none',
    functionName: frame.functionName,
    location: frame.location,
    score,
    selfTimePerOpUs: frame.selfTimePerOpUs,
  }
}

export function rankRuntimeFrames(result: ScenarioResult, operations: number) {
  const deopts = measurementDeopts(result.deopts)
  const allocByKey = new Map<string, number>()

  for (const [key, frame] of result.allocFrames.entries()) {
    allocByKey.set(key, frame.allocatedBytes / operations)
  }

  const merged = [...result.frames.entries()].map(([key, frame]): MergedFrame => ({
    allocBytesPerOp: allocByKey.get(key) ?? 0,
    functionName: frame.functionName,
    location: frame.location,
    selfTimePerOpUs: frame.selfTime / operations,
  }))

  const maxAlloc = Math.max(1, ...merged.map((frame) => frame.allocBytesPerOp))
  const maxDeopt = Math.max(1, ...deopts.counts.values())

  return merged
    .map((frame) => scoreFrame(frame, deopts, maxAlloc, maxDeopt))
    .sort((left, right) => right.score - left.score)
    .slice(0, 20)
    .map((entry, index) => ({
      allocBytesPerOp: entry.allocBytesPerOp,
      deoptSignals: entry.deoptSignals,
      functionName: entry.functionName,
      location: entry.location,
      rank: index + 1,
      selfTimePerOpUs: entry.selfTimePerOpUs,
    }))
}

type RankedFrames = ReturnType<typeof rankRuntimeFrames>

function formatUs(us: number): string {
  if (us >= 1000) return `${(us / 1000).toFixed(2)} ms`
  return `${us.toFixed(2)} µs`
}

function formatBytesPerOp(bytes: number): string {
  const perKOp = bytes * 1000

  if (perKOp >= 1024) return `${(perKOp / 1024).toFixed(1)} KB/kop`
  if (perKOp >= 1) return `${perKOp.toFixed(0)} B/kop`
  return '—'
}

export function generateReadingGuide(target: string): string {
  return [
    `# Reading the ${target} profile`,
    '',
    '- **Per-op** values divide the measured totals by the number of logical operations.',
    `  One harness batch executes ${BATCH_SIZE} operations, so total operations = measurement batches × ${BATCH_SIZE}.`,
    '- **CPU self-time** is sampled V8 on-CPU time attributed to the frame itself.',
    '- **Alloc/kop** estimates allocations during measurement, including subsequently collected objects.',
    '- CPU and heap sampling start after warmup in the same process; setup and validation are excluded.',
    '- **Deopt signals** include startup, warmup, and measurement in the separate trace pass.',
  ].join('\n')
}

function timingSection(runtime: ScenarioResult, batches: number, operations: number): string[] {
  const gcPercent = runtime.totalTime > 0 ? (100 * runtime.gcTimeUs) / runtime.totalTime : 0
  return [
    '## Scenario timing',
    '',
    '| Total time | Per-batch | Per-op | GC time | GC % |',
    '| --- | --- | --- | --- | --- |',
    `| ${formatUs(runtime.totalTime)} | ${formatUs(runtime.totalTime / batches)} | ${formatUs(runtime.totalTime / operations)} | ${formatUs(runtime.gcTimeUs)} | ${gcPercent.toFixed(1)}% |`,
    '',
  ]
}

function coverageSection(runtime: ScenarioResult): string[] {
  return [
    '## Attribution coverage',
    '',
    'Inclusive costs include descendant work and overlap between callers. Recursive source frames count once per sample. Unmapped includes native frames and frames without a source-map match.',
    '',
    '| Samples | Total | Project self | Other mapped | Unmapped/native |',
    '| --- | ---: | ---: | ---: | ---: |',
    ...(
      [
        ['CPU microseconds', runtime.cpuAttribution.coverage],
        ['Sampled bytes', runtime.heapAttribution.coverage],
      ] as const
    ).map(
      ([label, coverage]) =>
        `| ${label} | ${coverage.total} | ${coverage.project} | ${coverage.mapped} | ${coverage.unmapped} |`,
    ),
    '',
  ]
}

function inclusiveSections(runtime: ScenarioResult, operations: number): string[] {
  return [
    '## Inclusive project callers',
    '',
    '| Function | Location | Inclusive CPU/op |',
    '| --- | --- | ---: |',
    ...[...runtime.frames.values()]
      .sort((a, b) => b.inclusiveTime - a.inclusiveTime)
      .slice(0, 20)
      .map(
        (frame) =>
          `| ${frame.functionName} | ${frame.location} | ${formatUs(frame.inclusiveTime / operations)} |`,
      ),
    '',
    '## Inclusive allocation callers',
    '',
    '| Function | Location | Inclusive sampled allocation |',
    '| --- | --- | ---: |',
    ...[...runtime.allocFrames.values()]
      .sort((a, b) => b.inclusiveBytes - a.inclusiveBytes)
      .slice(0, 20)
      .map(
        (frame) =>
          `| ${frame.functionName} | ${frame.location} | ${formatBytesPerOp(frame.inclusiveBytes / operations)} |`,
      ),
    '',
  ]
}

function rankedSection(ranked: RankedFrames): string[] {
  if (ranked.length === 0) return ['No ranked frames.', '']
  return [
    '| Rank | Function | Location | Self-time/op | Alloc/kop | Deopt signals |',
    '| --- | --- | --- | --- | --- | --- |',
    ...ranked.map(
      (entry) =>
        `| ${entry.rank} | ${entry.functionName} | ${entry.location} | ${formatUs(entry.selfTimePerOpUs)} | ${formatBytesPerOp(entry.allocBytesPerOp)} | ${entry.deoptSignals} |`,
    ),
    '',
  ]
}

function allocationSection(runtime: ScenarioResult, operations: number): string[] {
  const topAllocations = [...runtime.allocFrames.values()]
    .sort((left, right) => right.allocatedBytes - left.allocatedBytes)
    .slice(0, 20)
  if (topAllocations.length === 0)
    return ['No project-level allocations attributed by the heap profiler.', '']
  return [
    '| Function | Location | Alloc/kop |',
    '| --- | --- | --- |',
    ...topAllocations.map(
      (frame) =>
        `| ${frame.functionName} | ${frame.location} | ${formatBytesPerOp(frame.allocatedBytes / operations)} |`,
    ),
    '',
  ]
}

export function generateReport(
  target: string,
  runtime: ScenarioResult,
  ranked: ReturnType<typeof rankRuntimeFrames>,
  batches: number,
): string {
  const operations = batches * BATCH_SIZE
  return [
    `# ${target[0].toUpperCase() + target.slice(1)} profiling report`,
    '',
    `- Measurement batches: ${batches.toLocaleString()}`,
    `- Operations per batch: ${BATCH_SIZE}`,
    `- Total operations: ${operations.toLocaleString()}`,
    '',
    ...timingSection(runtime, batches, operations),
    ...coverageSection(runtime),
    ...inclusiveSections(runtime, operations),
    `Deopt parse coverage: ${runtime.deoptCoverage.parsed}/${runtime.deoptCoverage.total} events parsed; ${runtime.deoptCoverage.unparsed} unparsed events retained. Ranked signals below use only measurement-phase events.`,
    '',
    '## Ranked hot frames',
    '',
    ...rankedSection(ranked),
    '## Top allocation frames',
    '',
    ...allocationSection(runtime, operations),
  ].join('\n')
}
