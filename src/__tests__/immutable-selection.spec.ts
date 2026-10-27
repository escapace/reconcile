import { describe, expect, it } from 'vitest'
import { immutableHead, immutableSelections } from '../graph/immutable-selection'
import { produce } from '../produce'
import type { ImmutableProblem } from '../types'
import { compactFixture, immutableDomains, rankedSelections } from './fixtures/compact-immutable'
import type { CompactImmutableInput } from './fixtures/compact-immutable'
import { randomSource } from './fixtures/public-api-fuzz'

function fixture(rows: Array<Partial<CompactImmutableInput['rows'][number]>>): ImmutableProblem {
  return compactFixture({
    dependencies: rows.map(() => []),
    rows: rows.map((row, node) => ({
      children: [],
      eligible: true,
      fixed: false,
      proposed: 100 + node,
      storage: 200 + node,
      ...row,
    })),
  })
}

function reference(problem: ImmutableProblem): boolean[][] {
  const domains = immutableDomains(problem)
  return rankedSelections(domains).map((selection) =>
    selection.map((choice, node) => domains[node][choice].retained),
  )
}

describe('compact immutable selection', () => {
  it('preserves the empty assignment and all-fresh boundary', () => {
    expect([...immutableSelections(fixture([]))]).toEqual([[]])
    expect([...immutableSelections(fixture([{ eligible: false }, { eligible: false }]))]).toEqual([
      [false, false],
    ])
  })

  it('orders complete masks by retention score and then keep-before-fresh', () => {
    expect([...immutableSelections(fixture([{}, {}]))]).toEqual([
      [true, true],
      [true, false],
      [false, true],
      [false, false],
    ])
  })

  it('retains mandatory specials or reports no assignment', () => {
    expect([...immutableSelections(fixture([{ fixed: true }, {}]))]).toEqual([
      [true, true],
      [true, false],
    ])
    expect([...immutableSelections(fixture([{ eligible: false, fixed: true }]))]).toEqual([])
  })

  it('keeps cyclic retentions closed, including self and repeated edges', () => {
    const problem = fixture([{ children: [0, 1, 1] }, { children: [0] }])
    expect([...immutableSelections(problem)]).toEqual([
      [true, true],
      [false, false],
    ])
  })

  it('restores older forward demands across repeated edges and backtracking', () => {
    const problem = fixture([{ children: [3, 3] }, { children: [3] }, {}, {}])
    const masks = [...immutableSelections(problem)]
    expect(masks[0]).toEqual([true, true, true, true])
    expect(masks).toEqual(reference(problem))
    expect(new Set(masks).size).toBe(masks.length)
  })

  it('preserves the complete stream for two cycles under one parent', () => {
    const size = 12
    const rows: Array<Partial<CompactImmutableInput['rows'][number]>> = [
      { children: [1, size + 1] },
    ]
    for (let copy = 0; copy < 2; copy += 1)
      for (let node = 0; node < size; node += 1)
        rows.push({ children: [1 + copy * size + ((node + 1) % size)] })
    const problem = fixture(rows)
    const masks = [...immutableSelections(problem)]
    const cycle = (kept: boolean): boolean[] => new Array<boolean>(size).fill(kept)
    expect(masks).toEqual([
      [true, ...cycle(true), ...cycle(true)],
      [false, ...cycle(true), ...cycle(true)],
      [false, ...cycle(true), ...cycle(false)],
      [false, ...cycle(false), ...cycle(true)],
      [false, ...cycle(false), ...cycle(false)],
    ])
    expect(masks).toEqual(reference(problem))
  })

  // CompactImmutable.ranked_head: an admissible, separated and closed eligibility mask is the
  // stream's first mask. Records have distinct storages and eligibility closed over parents, as
  // compileImmutable builds them, so the head needs only every fixed record to be eligible.
  it('streams the eligibility mask first when every fixed record is eligible', () => {
    const random = randomSource(91_357, 8).next
    let heads = 0
    let declined = 0
    for (let test = 0; test < 3000; test += 1) {
      const size = random(6)
      const rows = Array.from({ length: size }, () => ({
        children: Array.from({ length: random(3) === 0 ? 1 + random(2) : 0 }, () => random(size)),
        eligible: random(4) !== 0,
        fixed: random(5) === 0,
      }))
      // A record with an ineligible child is ineligible, as the closure of the unavailable makes it.
      for (let changed = true; changed;) {
        changed = false
        for (const row of rows)
          if (row.eligible && row.children.some((child) => !rows[child].eligible)) {
            row.eligible = false
            changed = true
          }
      }
      const problem = fixture(rows)
      const stream = [...immutableSelections(problem)]
      const head = immutableHead(problem)
      if (head === undefined) {
        declined += 1
        continue
      }
      heads += 1
      expect(stream[0], `fixture ${test}`).toEqual(head)
    }
    expect(heads).toBeGreaterThan(300)
    expect(declined).toBeGreaterThan(300)
  })

  it('preserves maximal reuse after undo rather than treating dirty state as failure', () => {
    const current = { n: 0 }
    const result = produce(current, (draft) => {
      draft.n = 1
      draft.n = 0
      return draft
    })
    expect(result).toBe(current)
    expect(current.n).toBe(0)
  })

  it('keeps unchanged settled Date identities', () => {
    const current = { date: new Date(7), n: 0 }
    expect(produce(current, (draft) => draft)).toBe(current)
  })
})
