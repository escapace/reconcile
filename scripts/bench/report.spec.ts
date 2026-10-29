import { describe, expect, it } from 'vitest'
import type { ScenarioSummary } from './ab'
import { verdict, type AbRound } from './report'
import type { Reading } from './stats'

/** A round of one kind that read `reading` on scenario `a`. */
function round(kind: string, reading: Reading): AbRound {
  const summary: ScenarioSummary = {
    controlMedianUsPerOperation: 1,
    fasterPairs: 0,
    medianPairedPercentChange: 0,
    medianPairedPercentInterval: null,
    pairedPercentChanges: [],
    reading,
    treeMedianUsPerOperation: 1,
  }
  return { kind, name: kind, source: 'source', summary: { a: summary } }
}

describe('verdict', () => {
  it('keeps a change only when two deciding rounds or more all read faster', () => {
    expect(verdict([round('deciding', 'faster')], 'a')).toMatch(/^no loss; as the target/)
    expect(verdict([round('deciding', 'faster'), round('deciding', 'faster')], 'a')).toMatch(
      /^faster/,
    )
    const retried = ['faster', 'unresolved', 'faster'] as const
    expect(
      verdict(
        retried.map((reading) => round('deciding', reading)),
        'a',
      ),
    ).toMatch(/^no loss/)
  })

  it('rejects a change that a deciding round reads slower', () => {
    const rounds = [
      round('deciding', 'faster'),
      round('deciding', 'faster'),
      round('deciding', 'slower'),
    ]
    expect(verdict(rounds, 'a')).toMatch(/^rejected/)
  })

  it('asks for a deciding round when a guard round reads slower', () => {
    expect(verdict([round('default', 'slightly slower')], 'a')).toMatch(/^needs a deciding round/)
    expect(verdict([round('small', 'unresolved')], 'a')).toBe('no loss in its rounds')
  })
})
