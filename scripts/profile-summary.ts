import assert from 'node:assert/strict'
import { readFileSync } from 'node:fs'
import path from 'node:path'
import type { attribute } from './profile-attribution'
import type { AllocAggregate } from './profile-frames'

type Counts = Record<string, number>
type Coverage = ReturnType<typeof attribute>['coverage']

/** The result fields that comparisons read from a single-pass summary.json. */
interface SampleResult {
  allocations?: AllocAggregate[]
  attribution?: ReturnType<typeof attribute>
  counts?: Counts
  gcTimeUs?: number
  microsecondsPerOperation?: number
  totalTime?: number
}

/** A sample's summary.json: a single-pass summary has `result`, an `all` summary has the rest. */
interface SampleSummary {
  allocations?: AllocAggregate[]
  gcTimeUs?: number
  heapAttribution?: ReturnType<typeof attribute>
  profiledTimeUs?: number
  result?: SampleResult
}

type MetricRead = (
  summary: SampleSummary,
  result: SampleResult,
  operations: number,
) => number | undefined

const IDENTITY_COUNTERS = ['classification.full', 'classification.expected', 'storage.probes']

function recordLine(log: string, prefix: string, message: string): unknown {
  const line = log.split('\n').find((line) => line.startsWith(prefix))
  assert(line !== undefined, message)
  return JSON.parse(line.slice(prefix.length))
}

/** Reads the counter record that the instrumented harness prints after measurement. */
export const counterRecord = (log: string): Record<string, number> =>
  recordLine(log, 'RECONCILE_COUNTS ', 'Counter record missing') as Counts

/** Instrumented sites that never ran still report zero. */
function zeroFillSites(counts: Counts, counterSites: Record<string, Counts>): void {
  for (const sites of Object.values(counterSites))
    for (const key of Object.keys(sites)) counts[key] ??= 0
}

function assertCounters(counts: Counts): void {
  for (const count of Object.values(counts))
    assert(Number.isSafeInteger(count) && count >= 0, 'Invalid counter')
}

function addMemoHits(counts: Counts): void {
  if ('classification.memoLookups' in counts && 'classification.memoMiss' in counts) {
    counts['classification.memoHits'] =
      counts['classification.memoLookups'] - counts['classification.memoMiss']
    assert(counts['classification.memoHits'] >= 0)
  }
}

function zeroFillIdentity(counts: Counts, key: string): void {
  counts[`${key}.identities`] ??= 0
  counts[`${key}.maximumPerIdentity`] ??= 0
}

export function countsResult(
  counts: Record<string, number>,
  counterSites: Record<string, Record<string, number>>,
  operations: number,
) {
  zeroFillSites(counts, counterSites)
  assertCounters(counts)
  addMemoHits(counts)
  for (const key of IDENTITY_COUNTERS) if (key in counts) zeroFillIdentity(counts, key)
  return {
    counts,
    operations,
    scope:
      'Exact instrumented events; allocation counters describe source constructions, not physical V8 allocations. Counter sites are recorded in build.json. Counting time is not throughput.',
  }
}

export function timeResult(log: string, operations: number) {
  const timing = recordLine(log, 'RECONCILE_TIME ', 'Measurement record missing') as {
    elapsedMs: number
    operations: number
  }
  assert(Number.isFinite(timing.elapsedMs) && timing.elapsedMs >= 0)
  assert.equal(timing.operations, operations)
  return {
    ...timing,
    microsecondsPerOperation: (timing.elapsedMs * 1000) / timing.operations,
  }
}

const perOperation = (value: number | undefined, operations: number): number | undefined =>
  value === undefined ? undefined : value / operations

const projectBytes = (allocations: AllocAggregate[] | undefined): number | undefined =>
  allocations === undefined
    ? undefined
    : allocations.reduce((total, entry) => total + entry.allocatedBytes, 0)

/** Single-pass heap summaries carry their coverage on `result.attribution`. */
const resultCoverage = (result: SampleResult): Coverage | undefined =>
  result.allocations === undefined ? undefined : result.attribution?.coverage

const totalBytes = (coverage: Coverage | undefined, operations: number): number | undefined =>
  coverage === undefined ? undefined : coverage.total / operations

/** Comparison metrics in report order; an absent source omits its metric. */
const sampleMetricReads: ReadonlyArray<readonly [string, MetricRead]> = [
  ['latencyUsPerOperation', (_, result) => result.microsecondsPerOperation],
  [
    'sampledGCUsPerOperation',
    (summary, result, operations) => perOperation(result.gcTimeUs ?? summary.gcTimeUs, operations),
  ],
  [
    'profiledUsPerOperation',
    (summary, result, operations) =>
      perOperation(result.totalTime ?? summary.profiledTimeUs, operations),
  ],
  [
    'sampledProjectBytesPerOperation',
    (summary, result, operations) =>
      perOperation(projectBytes(result.allocations ?? summary.allocations), operations),
  ],
  [
    'sampledTotalBytesPerOperation',
    (summary, result, operations) =>
      totalBytes(summary.heapAttribution?.coverage ?? resultCoverage(result), operations),
  ],
]

function countMetric(key: string, count: number, operations: number): [string, number] {
  const identityMetric = key.endsWith('.identities') || key.endsWith('.maximumPerIdentity')
  return [
    `count.${key}.${identityMetric ? 'perMeasurement' : 'perOperation'}`,
    identityMetric ? count : count / operations,
  ]
}

function addSampleMetrics(
  metrics: Counts,
  summary: SampleSummary,
  result: SampleResult,
  operations: number,
): void {
  for (const [name, read] of sampleMetricReads) {
    const value = read(summary, result, operations)
    if (value !== undefined) metrics[name] = value
  }
}

function addCountMetrics(metrics: Counts, counts: Counts, operations: number): void {
  for (const [key, count] of Object.entries(counts)) {
    const [name, value] = countMetric(key, count, operations)
    metrics[name] = value
  }
}

/** Reads one sample's summary.json and normalizes its metrics per logical operation. */
export function readSampleMetrics(directory: string, operations: number): Record<string, number> {
  const summary = JSON.parse(
    readFileSync(path.join(directory, 'summary.json'), 'utf8'),
  ) as SampleSummary
  const result = summary.result ?? {}
  const metrics: Counts = {}
  addSampleMetrics(metrics, summary, result, operations)
  addCountMetrics(metrics, result.counts ?? {}, operations)
  return metrics
}

function distribution(numbers: number[]) {
  const ordered = numbers.filter((value) => Number.isFinite(value)).toSorted((a, b) => a - b)
  if (ordered.length === 0) return { count: 0 }
  const middle = Math.floor(ordered.length / 2)
  return {
    count: ordered.length,
    max: ordered.at(-1),
    median:
      ordered.length % 2 === 0 ? (ordered[middle - 1] + ordered[middle]) / 2 : ordered[middle],
    min: ordered[0],
  }
}

/** Median, minimum and maximum of every metric, per compared source. */
export function comparisonMetrics(
  samples: ReadonlyArray<{
    readonly label: 'baseline' | 'candidate'
    readonly metrics: Readonly<Record<string, number>>
  }>,
) {
  const names = [...new Set(samples.flatMap((sample) => Object.keys(sample.metrics)))]
  const observed = (label: 'baseline' | 'candidate', name: string): number[] =>
    samples.filter((sample) => sample.label === label).map((sample) => sample.metrics[name])
  return Object.fromEntries(
    names.map((name) => [
      name,
      {
        baseline: distribution(observed('baseline', name)),
        candidate: distribution(observed('candidate', name)),
      },
    ]),
  )
}
