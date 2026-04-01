/**
 * Object-kind profiling workflow.
 *
 * Bundles the profiling harness with esbuild, profiles one configured target,
 * prints the results to stdout, and removes temporary profiler
 * artifacts before exiting.
 *
 * Usage:
 *   pnpm profile
 */

import assert from 'node:assert/strict'
import { execFileSync } from 'node:child_process'
import { randomBytes } from 'node:crypto'
import {
  existsSync,
  mkdirSync,
  mkdtempSync,
  readdirSync,
  readFileSync,
  rmSync,
  writeFileSync,
} from 'node:fs'
import { createRequire, SourceMap } from 'node:module'
import { tmpdir } from 'node:os'
import path from 'node:path'

import { BATCH_SIZE } from '../perf/scenarios'

const require = createRequire(import.meta.url)

interface ScenarioDefinition {
  name: string
}

interface TargetDefinition {
  name: string
}

interface WorkflowConfig {
  cpuProfIntervalUs: number
  harnessSource: string
  heapProfIntervalBytes: number
  measurementBatchCount: number
  root: string
  scenarios: ScenarioDefinition[]
  target: TargetDefinition
  timeout: number
  traceBatchCountLimit: number
  warmupBatchCount: number
}

interface ScenarioArtifacts {
  cpuprofilePath: string
  heapprofilePath: string
  traceLogPath: string
}

interface ResolvedFrame {
  functionName: string
  originalColumn: number
  originalLine: number
  originalSource: string
}

interface CPUProfileNode {
  callFrame: {
    columnNumber: number
    functionName: string
    lineNumber: number
    scriptId: string
    url: string
  }
  hitCount: number
  id: number
}

interface CPUProfile {
  endTime: number
  nodes: CPUProfileNode[]
  samples: number[]
  startTime: number
  timeDeltas: number[]
}

interface FrameAggregate {
  functionName: string
  location: string
  selfTime: number
  totalHits: number
}

interface CPUProfileResult {
  frames: Map<string, FrameAggregate>
  gcTimeUs: number
  totalTime: number
}

interface HeapProfileNode {
  callFrame: {
    columnNumber: number
    functionName: string
    lineNumber: number
    scriptId: string
    url: string
  }
  children: HeapProfileNode[]
  id: number
  selfSize: number
}

interface HeapProfile {
  head: HeapProfileNode
  samples: Array<{ nodeId: number; ordinal: number; size: number }>
}

interface AllocAggregate {
  allocatedBytes: number
  functionName: string
  location: string
}

interface DeoptEntry {
  count: number
  functionName: string
  reason: string
}

interface ScenarioResult {
  allocFrames: Map<string, AllocAggregate>
  cpuprofilePath: string
  deopts: DeoptEntry[]
  frames: Map<string, FrameAggregate>
  gcTimeUs: number
  heapprofilePath: string
  scenario: string
  totalTime: number
  traceLogPath: string
}

interface RankedTarget {
  allocBytesPerOp: number
  deoptSignals: string
  functionName: string
  location: string
  rank: number
  selfTimePerOpUs: number
}

const ROOT = path.resolve(import.meta.dirname, '..')

const targetArgument = process.argv[2]

if (targetArgument === undefined || targetArgument.trim() === '') {
  console.error('Usage: pnpm profile <target>')
  process.exit(1)
}

const target: TargetDefinition = {
  name: targetArgument,
}

const config: WorkflowConfig = {
  measurementBatchCount: 200,
  traceBatchCountLimit: 200,

  cpuProfIntervalUs: 100,
  harnessSource: path.join(ROOT, 'perf', 'profile-harness.ts'),
  heapProfIntervalBytes: 256,
  root: ROOT,
  scenarios: [{ name: target.name }],
  target,
  timeout: 120_000,
  warmupBatchCount: 5,
}

const CROCKFORD = '0123456789ABCDEFGHJKMNPQRSTVWXYZ'

function ulid(): string {
  const now = Date.now()
  const random = randomBytes(10)
  const time = new Array<string>(10)

  let remaining = now

  for (let index = 9; index >= 0; index -= 1) {
    time[index] = CROCKFORD[remaining & 0x1f]
    remaining = Math.floor(remaining / 32)
  }

  const rand = new Array<string>(16)
  let bitBuffer = 0
  let bitsInBuffer = 0
  let byteIndex = 0
  let charIndex = 0

  while (charIndex < 16) {
    if (bitsInBuffer < 5) {
      bitBuffer = (bitBuffer << 8) | random[byteIndex++]
      bitsInBuffer += 8
    }

    rand[charIndex++] = CROCKFORD[(bitBuffer >>> (bitsInBuffer - 5)) & 0x1f]
    bitsInBuffer -= 5
  }

  return time.join('') + rand.join('')
}

const ESBUILD_PATH = (() => {
  const pnpmDirectory = path.join(config.root, 'node_modules', '.pnpm')
  const candidates = readdirSync(pnpmDirectory).filter((directory) =>
    directory.startsWith('esbuild@'),
  )

  if (candidates.length === 0) {
    throw new Error('esbuild not found in pnpm store — is esroll installed?')
  }

  return path.join(pnpmDirectory, candidates[0], 'node_modules', 'esbuild')
})()

const runId = ulid()
const outputDirectory = mkdtempSync(path.join(tmpdir(), 'object-kind-profile-'))

function bundleHarness(): { bundlePath: string; sourceMap: SourceMap } {
  const bundlePath = path.join(outputDirectory, 'harness.mjs')

  const esbuild = require(ESBUILD_PATH) as {
    buildSync: (options: Record<string, unknown>) => void
  }

  esbuild.buildSync({
    bundle: true,
    entryPoints: [config.harnessSource],
    format: 'esm',
    outfile: bundlePath,
    platform: 'node',
    sourcemap: true,
    target: 'esnext',
  })

  const rawMap = JSON.parse(
    readFileSync(`${bundlePath}.map`, 'utf-8'),
  ) as import('node:module').SourceMapPayload

  return {
    bundlePath,
    sourceMap: new SourceMap(rawMap),
  }
}

function runScenario(scenario: string, bundlePath: string): ScenarioArtifacts {
  const rawDirectory = path.join(outputDirectory, 'raw')
  mkdirSync(rawDirectory, { recursive: true })

  const traceLogPath = path.join(rawDirectory, `${scenario}.trace.log`)
  const measuredArguments = [bundlePath, scenario, String(config.measurementBatchCount)]
  const warmupArguments =
    config.warmupBatchCount > 0
      ? [bundlePath, scenario, String(config.warmupBatchCount)]
      : undefined

  const warmupPass = (): void => {
    if (warmupArguments === undefined) {
      return
    }

    execFileSync(process.execPath, warmupArguments, {
      cwd: config.root,
      env: { ...process.env, NODE_NO_WARNINGS: '1' },
      stdio: ['ignore', 'ignore', 'ignore'],
      timeout: config.timeout,
    })
  }

  console.log(`  [cpu]  ${scenario}`)
  warmupPass()
  execFileSync(
    process.execPath,
    [
      '--cpu-prof',
      `--cpu-prof-dir=${rawDirectory}`,
      `--cpu-prof-name=${scenario}.cpuprofile`,
      `--cpu-prof-interval=${config.cpuProfIntervalUs}`,
      ...measuredArguments,
    ],
    {
      cwd: config.root,
      env: { ...process.env, NODE_NO_WARNINGS: '1' },
      stdio: ['ignore', 'ignore', 'ignore'],
      timeout: config.timeout,
    },
  )

  console.log(`  [heap] ${scenario}`)
  warmupPass()
  execFileSync(
    process.execPath,
    [
      '--heap-prof',
      `--heap-prof-dir=${rawDirectory}`,
      `--heap-prof-name=${scenario}.heapprofile`,
      `--heap-prof-interval=${config.heapProfIntervalBytes}`,
      ...measuredArguments,
    ],
    {
      cwd: config.root,
      env: { ...process.env, NODE_NO_WARNINGS: '1' },
      stdio: ['ignore', 'ignore', 'ignore'],
      timeout: config.timeout,
    },
  )

  warmupPass()

  try {
    const trace = execFileSync(
      process.execPath,
      [
        '--trace-opt',
        '--trace-deopt',
        bundlePath,
        scenario,
        String(Math.min(config.measurementBatchCount, config.traceBatchCountLimit)),
      ],
      {
        cwd: config.root,
        encoding: 'utf-8',
        env: { ...process.env, NODE_NO_WARNINGS: '1' },
        maxBuffer: 50 * 1024 * 1024,
        stdio: ['ignore', 'pipe', 'pipe'],
        timeout: config.timeout,
      },
    )

    writeFileSync(traceLogPath, trace)
  } catch (error: unknown) {
    const stderr =
      error !== null && typeof error === 'object' && 'stderr' in error
        ? String((error as { stderr: unknown }).stderr)
        : ''
    const stdout =
      error !== null && typeof error === 'object' && 'stdout' in error
        ? String((error as { stdout: unknown }).stdout)
        : ''
    writeFileSync(traceLogPath, stdout + '\n' + stderr)
  }

  const cpuprofilePath = path.join(rawDirectory, `${scenario}.cpuprofile`)

  if (!existsSync(cpuprofilePath)) {
    const files = readdirSync(rawDirectory).filter(
      (file) => file.startsWith(scenario) && file.endsWith('.cpuprofile'),
    )

    if (files.length === 0) {
      throw new Error(`CPU profile not found for scenario "${scenario}" in ${rawDirectory}`)
    }

    return {
      cpuprofilePath: path.join(rawDirectory, files[0]),
      heapprofilePath: path.join(rawDirectory, `${scenario}.heapprofile`),
      traceLogPath,
    }
  }

  return {
    cpuprofilePath,
    heapprofilePath: path.join(rawDirectory, `${scenario}.heapprofile`),
    traceLogPath,
  }
}

function resolveFrame(
  callFrame: { columnNumber: number; functionName: string; lineNumber: number; url: string },
  bundlePath: string,
  sourceMap: SourceMap,
): ResolvedFrame | undefined {
  if (!callFrame.url.endsWith(path.basename(bundlePath))) {
    return undefined
  }

  const entry = sourceMap.findEntry(callFrame.lineNumber, callFrame.columnNumber)

  if (!('originalSource' in entry) || entry.originalSource === undefined) {
    return undefined
  }

  assert(typeof entry.originalSource === 'string')
  assert(typeof entry.originalLine === 'number')
  assert(typeof entry.originalColumn === 'number')

  const absPath = path.resolve(path.dirname(bundlePath), entry.originalSource)
  const relativePath = path.relative(config.root, absPath)

  if (relativePath.startsWith('..') || relativePath.includes('node_modules')) {
    return undefined
  }

  return {
    functionName: callFrame.functionName !== '' ? callFrame.functionName : '(anonymous)',
    originalColumn: entry.originalColumn + 1,
    originalLine: entry.originalLine + 1,
    originalSource: relativePath,
  }
}

function isProjectSource(source: string): boolean {
  return source.startsWith('src/')
}

function locationString(frame: ResolvedFrame): string {
  return `${frame.originalSource}:${frame.originalLine}:${frame.originalColumn}`
}

function parseCPUProfile(
  profilePath: string,
  bundlePath: string,
  sourceMap: SourceMap,
): CPUProfileResult {
  const raw = JSON.parse(readFileSync(profilePath, 'utf-8')) as CPUProfile
  const nodeById = new Map<number, CPUProfileNode>()

  for (const node of raw.nodes) {
    nodeById.set(node.id, node)
  }

  const gcNodeId = raw.nodes.find(
    (node) => node.callFrame.functionName === '(garbage collector)',
  )?.id
  const selfTimeById = new Map<number, number>()
  let gcTimeUs = 0

  for (let index = 0; index < raw.samples.length; index += 1) {
    const nodeId = raw.samples[index]
    const delta = raw.timeDeltas[index]
    selfTimeById.set(nodeId, (selfTimeById.get(nodeId) ?? 0) + delta)

    if (nodeId === gcNodeId) {
      gcTimeUs += delta
    }
  }

  const frames = new Map<string, FrameAggregate>()

  for (const [nodeId, selfTime] of selfTimeById.entries()) {
    const node = nodeById.get(nodeId)

    if (node === undefined) continue

    const resolved = resolveFrame(node.callFrame, bundlePath, sourceMap)

    if (resolved === undefined || !isProjectSource(resolved.originalSource)) {
      continue
    }

    const key = `${resolved.functionName}|${resolved.originalSource}|${resolved.originalLine}|${resolved.originalColumn}`
    const existing = frames.get(key)

    if (existing !== undefined) {
      existing.selfTime += selfTime
      existing.totalHits += node.hitCount
    } else {
      frames.set(key, {
        functionName: resolved.functionName,
        location: locationString(resolved),
        selfTime,
        totalHits: node.hitCount,
      })
    }
  }

  return {
    frames,
    gcTimeUs,
    totalTime: raw.timeDeltas.reduce((sum, delta) => sum + delta, 0),
  }
}

function parseHeapProfile(
  profilePath: string,
  bundlePath: string,
  sourceMap: SourceMap,
): Map<string, AllocAggregate> {
  const raw = JSON.parse(readFileSync(profilePath, 'utf-8')) as HeapProfile
  const aggregates = new Map<string, AllocAggregate>()

  const walkTree = (node: HeapProfileNode): void => {
    if (node.selfSize > 0) {
      const resolved = resolveFrame(node.callFrame, bundlePath, sourceMap)

      if (resolved !== undefined && isProjectSource(resolved.originalSource)) {
        const key = `${resolved.functionName}|${resolved.originalSource}|${resolved.originalLine}|${resolved.originalColumn}`
        const existing = aggregates.get(key)

        if (existing !== undefined) {
          existing.allocatedBytes += node.selfSize
        } else {
          aggregates.set(key, {
            allocatedBytes: node.selfSize,
            functionName: resolved.functionName,
            location: locationString(resolved),
          })
        }
      }
    }

    for (const child of node.children) {
      walkTree(child)
    }
  }

  walkTree(raw.head)

  return aggregates
}

function parseDeoptLog(logPath: string): DeoptEntry[] {
  if (!existsSync(logPath)) return []

  const content = readFileSync(logPath, 'utf-8')
  const deoptCounts = new Map<string, { count: number; reason: string }>()

  for (const line of content.split('\n')) {
    const deoptMatch = /\[deoptimizing\s+\([^)]*\):[^<]*<(\S+)>/.exec(line)
    const reasonMatch = /reason:\s*([^[\]]+)/.exec(line)

    if (deoptMatch === null || reasonMatch === null) {
      continue
    }

    const functionName = deoptMatch[1]
    const reason = reasonMatch[1].trim()
    const key = `${functionName}|${reason}`
    const existing = deoptCounts.get(key)

    if (existing !== undefined) {
      existing.count += 1
    } else {
      deoptCounts.set(key, { count: 1, reason })
    }
  }

  return [...deoptCounts.entries()]
    .map(([key, { count, reason }]) => ({
      count,
      functionName: key.split('|')[0],
      reason,
    }))
    .sort((left, right) => right.count - left.count)
}

function rankRuntimeFrames(result: ScenarioResult, operations: number): RankedTarget[] {
  const deoptByFunction = new Map<string, number>()
  const reasonsByFunction = new Map<string, string[]>()

  for (const entry of result.deopts) {
    deoptByFunction.set(
      entry.functionName,
      (deoptByFunction.get(entry.functionName) ?? 0) + entry.count,
    )
    const reasons = reasonsByFunction.get(entry.functionName) ?? []

    if (!reasons.includes(entry.reason)) {
      reasons.push(entry.reason)
      reasonsByFunction.set(entry.functionName, reasons)
    }
  }

  const allocByKey = new Map<string, number>()

  for (const [key, frame] of result.allocFrames.entries()) {
    allocByKey.set(key, frame.allocatedBytes / operations)
  }

  const merged = [...result.frames.entries()].map(([key, frame]) => ({
    allocBytesPerOp: allocByKey.get(key) ?? 0,
    functionName: frame.functionName,
    location: frame.location,
    selfTimePerOpUs: frame.selfTime / operations,
  }))

  const maxAlloc = Math.max(1, ...merged.map((frame) => frame.allocBytesPerOp))
  const maxDeopt = Math.max(1, ...deoptByFunction.values())

  return merged
    .map((frame) => {
      const deoptCount = deoptByFunction.get(frame.functionName) ?? 0
      const reasons = reasonsByFunction.get(frame.functionName) ?? []
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
    })
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

function formatTargetLabel(target: TargetDefinition): string {
  return target.name[0].toUpperCase() + target.name.slice(1)
}

function generateReadingGuide(target: TargetDefinition): string {
  return [
    `# Reading the ${target.name} profile`,
    '',
    '- **Per-op** values divide the measured totals by the number of logical operations.',
    `  One harness batch executes ${BATCH_SIZE} operations, so total operations = measurement batches × ${BATCH_SIZE}.`,
    '- **CPU self-time** is sampled V8 on-CPU time attributed to the frame itself.',
    '- **Alloc/kop** comes from the sampled V8 heap profiler and is approximate.',
    '- **Deopt signals** summarize V8 deoptimization events seen during the trace pass.',
  ].join('\n')
}

function generateReport(
  target: TargetDefinition,
  runtime: ScenarioResult,
  ranked: RankedTarget[],
): string {
  const operations = config.measurementBatchCount * BATCH_SIZE
  const runtimePerOp = runtime.totalTime / operations
  const runtimePerBatch = runtime.totalTime / config.measurementBatchCount
  const gcPercent = runtime.totalTime > 0 ? (100 * runtime.gcTimeUs) / runtime.totalTime : 0
  const topAllocations = [...runtime.allocFrames.values()]
    .sort((left, right) => right.allocatedBytes - left.allocatedBytes)
    .slice(0, 20)

  const lines: string[] = []

  lines.push(`# ${formatTargetLabel(target)} profiling report`)
  lines.push('')
  lines.push(`- Measurement batches: ${config.measurementBatchCount.toLocaleString()}`)
  lines.push(`- Operations per batch: ${BATCH_SIZE}`)
  lines.push(`- Total operations: ${operations.toLocaleString()}`)
  lines.push('')

  lines.push('## Scenario timing')
  lines.push('')
  lines.push('| Total time | Per-batch | Per-op | GC time | GC % |')
  lines.push('| --- | --- | --- | --- | --- |')
  lines.push(
    `| ${formatUs(runtime.totalTime)} | ${formatUs(runtimePerBatch)} | ${formatUs(runtimePerOp)} | ${formatUs(runtime.gcTimeUs)} | ${gcPercent.toFixed(1)}% |`,
  )
  lines.push('')

  lines.push('## Ranked hot frames')
  lines.push('')

  if (ranked.length === 0) {
    lines.push('No ranked frames.')
    lines.push('')
  } else {
    lines.push('| Rank | Function | Location | Self-time/op | Alloc/kop | Deopt signals |')
    lines.push('| --- | --- | --- | --- | --- | --- |')

    for (const entry of ranked) {
      lines.push(
        `| ${entry.rank} | ${entry.functionName} | ${entry.location} | ${formatUs(entry.selfTimePerOpUs)} | ${formatBytesPerOp(entry.allocBytesPerOp)} | ${entry.deoptSignals} |`,
      )
    }

    lines.push('')
  }

  lines.push('## Top allocation frames')
  lines.push('')

  if (topAllocations.length === 0) {
    lines.push('No project-level allocations attributed by the heap profiler.')
    lines.push('')
  } else {
    lines.push('| Function | Location | Alloc/kop |')
    lines.push('| --- | --- | --- |')

    for (const frame of topAllocations) {
      lines.push(
        `| ${frame.functionName} | ${frame.location} | ${formatBytesPerOp(frame.allocatedBytes / operations)} |`,
      )
    }

    lines.push('')
  }

  return lines.join('\n')
}

try {
  console.log('Context-runtime profiling workflow')
  console.log(`Run ID:  ${runId}`)
  console.log('')
  console.log('  [build] bundling harness with esbuild')

  const { bundlePath, sourceMap } = bundleHarness()
  const results = new Map<string, ScenarioResult>()

  console.log(
    `  [run]  ${config.measurementBatchCount.toLocaleString()} measurement batches, ${config.warmupBatchCount.toLocaleString()} warmup batches, ${BATCH_SIZE} ops/batch`,
  )

  for (const { name } of config.scenarios) {
    const artifacts = runScenario(name, bundlePath)
    const cpuResult = parseCPUProfile(artifacts.cpuprofilePath, bundlePath, sourceMap)

    results.set(name, {
      allocFrames: parseHeapProfile(artifacts.heapprofilePath, bundlePath, sourceMap),
      cpuprofilePath: artifacts.cpuprofilePath,
      deopts: parseDeoptLog(artifacts.traceLogPath),
      frames: cpuResult.frames,
      gcTimeUs: cpuResult.gcTimeUs,
      heapprofilePath: artifacts.heapprofilePath,
      scenario: name,
      totalTime: cpuResult.totalTime,
      traceLogPath: artifacts.traceLogPath,
    })
  }

  console.log('')

  const runtime = results.get(config.target.name)

  assert(runtime !== undefined, `scenario "${config.target.name}" not found in results`)

  const operations = config.measurementBatchCount * BATCH_SIZE
  const ranked = rankRuntimeFrames(runtime, operations)

  console.log(`===== ${config.target.name.toUpperCase()} =====`)
  console.log('')
  console.log(generateReadingGuide(config.target))
  console.log('')
  console.log(generateReport(config.target, runtime, ranked))
  console.log('')
  console.log('Done.')
} finally {
  rmSync(outputDirectory, { force: true, recursive: true })
}
