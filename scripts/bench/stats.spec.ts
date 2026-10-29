import { readFileSync } from 'node:fs'
import path from 'node:path'
import { describe, expect, it } from 'vitest'
import { summarize, type Row, type ScenarioSummary } from './ab'
import { batchCounts, estimateSeconds, interval, roundHalfEven } from './stats'

/** Two rounds that the Python driver this port replaces sampled and summarized: a default round
 * and a deciding one. */
const fixtures = ['ab-default', 'ab-deciding'].map(
  (name) =>
    JSON.parse(
      readFileSync(path.join(import.meta.dirname, 'fixtures', `${name}.json`), 'utf8'),
    ) as {
      rows: Row[]
      summary: Record<string, ScenarioSummary>
    },
)

describe('summarize', () => {
  it.each(
    fixtures.flatMap((fixture) =>
      Object.keys(fixture.summary).map((scenario) => [scenario, fixture] as const),
    ),
  )('reproduces the Python summary of %s exactly', (scenario, { rows, summary }) => {
    expect(summarize(rows, scenario)).toEqual(summary[scenario])
  })
})

describe('the round arithmetic', () => {
  it('draws the bootstrap interval of Python with its seed', () => {
    expect(interval([1, -2, 3, 0.5, -1.5, 2.5, 0, 4, -3, 1.5])).toEqual([-1.25, 2.25])
    expect(interval([1, 2, 3])).toBeUndefined()
  })

  it('rounds halves to even, as Python does', () => {
    expect([62.5, 63.5, 2.4, 2.6].map(roundHalfEven)).toEqual([62, 64, 2, 3])
  })

  it('sizes batches and estimates the sampling time as the Python driver did', () => {
    const preflight = [
      { elapsedMs: 50, scenario: 'a', wallSeconds: 0.4 },
      { elapsedMs: 40, scenario: 'a', wallSeconds: 0.35 },
      { elapsedMs: 12.5, scenario: 'b', wallSeconds: 0.2 },
      { elapsedMs: 13, scenario: 'b', wallSeconds: 0.21 },
    ]
    const counts = batchCounts(preflight, 'auto', 'auto', 0.5)
    expect(counts).toEqual({ a: { batches: 62, warmup: 31 }, b: { batches: 200, warmup: 100 } })
    expect(estimateSeconds(preflight, 10, counts)).toBe(41.32999999999999)
    expect(batchCounts(preflight, 7, 'auto', 0.5)).toEqual({
      a: { batches: 7, warmup: 3 },
      b: { batches: 7, warmup: 3 },
    })
  })
})
