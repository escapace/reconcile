import assert from 'node:assert/strict'

type Counts = Record<string, number>

const IDENTITY_COUNTERS = ['classification.full', 'classification.expected']

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
      'Exact instrumented events; allocation counters describe source constructions, not physical V8 allocations. Counting time is not throughput.',
  }
}

/** The counters whose counts differ between two runs, as `[baseline, candidate]`; a counter
 * one run lacks is `null` there. */
export function countChanges(
  baseline: Record<string, number>,
  candidate: Record<string, number>,
): Record<string, [number | null, number | null]> {
  const names = [...new Set([...Object.keys(baseline), ...Object.keys(candidate)])].toSorted()
  return Object.fromEntries(
    names
      .filter((name) => baseline[name] !== candidate[name])
      .map((name) => [name, [baseline[name] ?? null, candidate[name] ?? null]]),
  )
}
