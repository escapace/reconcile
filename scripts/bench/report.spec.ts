import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import path from 'node:path'
import { afterAll, describe, expect, it } from 'vitest'
import type { ScenarioSummary } from './ab'
import type { Experiment } from './experiments'
import { report, verdict, type AbRound } from './report'
import type { Reading } from './stats'

/** A round's summary of scenario `a`. */
const summaryOf = (reading: Reading, change = 0): ScenarioSummary => ({
  controlMedianUsPerOperation: 1,
  fasterPairs: 0,
  medianPairedPercentChange: change,
  medianPairedPercentInterval: null,
  pairedPercentChanges: [],
  reading,
  treeMedianUsPerOperation: 1,
})

/** A round of one kind that read `reading` on scenario `a`. */
const round = (kind: string, reading: Reading): AbRound => ({
  kind,
  name: kind,
  source: 'source',
  summary: { a: summaryOf(reading) },
})

/** The plan of an A/B round of `kind` from sources `tree` against `control`. */
const plan = (kind: string, control = 'control', tree = 'change', frozen = ['w', 'w']) => ({
  frozenWorkloadSha256: { control: frozen[0], tree: frozen[1] },
  kind,
  sharedWorkloadSha256: 's',
  size: 256,
  sourceSha256: { control, tree },
})

/** The plan of a size comparison of `tree` against `control`. */
const sizes = (control: string, tree: string) => ({
  plan: { modules: null, sourceSha256: { control, tree } },
})

describe('verdict', () => {
  it('keeps a change only when two deciding rounds or more all read faster', () => {
    expect(verdict([round('deciding', 'faster')], 'a')).toMatch(/^not rejected: .*1 faster/)
    expect(verdict([round('deciding', 'faster'), round('deciding', 'faster')], 'a')).toMatch(
      /^faster/,
    )
    const retried = ['faster', 'unresolved', 'faster'] as const
    expect(
      verdict(
        retried.map((reading) => round('deciding', reading)),
        'a',
      ),
    ).toMatch(/^not rejected/)
  })

  it('rejects a change that a deciding round reads slower, and names one slightly slower', () => {
    const rounds = [
      round('deciding', 'faster'),
      round('deciding', 'faster'),
      round('deciding', 'slower'),
    ]
    expect(verdict(rounds, 'a')).toMatch(/^rejected/)
    expect(
      verdict([round('default', 'slower'), round('deciding', 'slightly slower')], 'a'),
    ).toMatch(/^not rejected: .*1 slightly slower within the guard/)
  })

  it('asks for a deciding round when a guard round reads slower, and claims nothing from too few pairs', () => {
    expect(verdict([round('default', 'slightly slower')], 'a')).toMatch(/^needs a deciding round/)
    expect(verdict([round('small', 'unresolved')], 'a')).toBe('no round reads slower')
    expect(verdict([round('custom', 'too few pairs')], 'a')).toMatch(/^no evidence/)
  })
})

describe('report', () => {
  const root = mkdtempSync(path.join(tmpdir(), 'reconcile-report-spec-'))
  afterAll(() => {
    rmSync(root, { force: true, recursive: true })
  })

  /** An experiment whose control's sources are pinned as `control`, holding `rounds`. */
  function experimentWith(
    rounds: ReadonlyArray<{ plan: object; status?: string; summary?: object }>,
  ): Experiment {
    const directory = mkdtempSync(path.join(root, 'experiment-'))
    rounds.forEach(({ plan, status = 'passed', summary }, index) => {
      const folder = path.join(directory, 'rounds', `${index}-ab`)
      mkdirSync(folder, { recursive: true })
      writeFileSync(path.join(folder, 'plan.json'), JSON.stringify(plan))
      writeFileSync(path.join(folder, 'receipt.json'), JSON.stringify({ status }))
      if (summary !== undefined)
        writeFileSync(path.join(folder, 'summary.json'), JSON.stringify(summary))
    })
    const record = { commit: 'abc', created: 'then', sourceSha256: 'control', worktree: false }
    return { directory, name: 'spec', record, tree: path.join(directory, 'tree') }
  }

  const faster = { reconcile: summaryOf('faster', -5) }

  it('judges only passed rounds against the frozen control with the same workloads', () => {
    const text = report(
      experimentWith([
        { plan: plan('deciding'), summary: faster },
        { plan: plan('deciding', 'edited control'), summary: faster },
        { plan: plan('deciding', 'control', 'change', ['w', 'other']), summary: faster },
        { plan: plan('deciding'), status: 'failed', summary: faster },
      ]),
    )
    expect(text).toContain('1 round against another control than the one frozen, not judged.')
    expect(text).toContain('1 round whose trees ran different frozen workloads, not judged.')
    expect(text).toMatch(/reconcile +not rejected/)
  })

  it('counts a round of identical sources as A/A, whatever kind it was recorded as', () => {
    const text = report(
      experimentWith([{ plan: plan('default', 'control', 'control'), summary: faster }]),
    )
    expect(text).toContain('1 A/A round measures noise.')
    expect(text).toContain('No A/B round of a change yet')
  })

  it('asks for a size comparison of the judged sources against the frozen control', () => {
    const stale = report(
      experimentWith([{ plan: plan('default'), summary: faster }, sizes('control', 'older')]),
    )
    expect(stale).toContain('a size comparison of these sources')
    const current = report(
      experimentWith([{ plan: plan('default'), summary: faster }, sizes('control', 'change')]),
    )
    expect(current).not.toContain('size comparison')
  })
})
