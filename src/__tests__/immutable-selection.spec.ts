import { describe, expect, it } from 'vitest'
import { reactive, shallowReactive } from 'vue'
import { storageIdentity } from '../adapters/vue'
import { immutableSelections } from '../graph/immutable-selection'
import { selections } from '../graph/selection'
import { produce } from '../produce'
import type { ImmutableProblem } from '../types'
import { compactFixture, immutableDomains } from './fixtures/compact-immutable'
import type { CompactImmutableInput } from './fixtures/compact-immutable'

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
  return [...selections(domains)].map((selection) =>
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

  it('separates shared owners without losing the equal-score tie order', () => {
    expect([...immutableSelections(fixture([{ storage: 200 }, { storage: 200 }]))]).toEqual([
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
    expect([
      ...immutableSelections(
        fixture([
          { fixed: true, storage: 200 },
          { fixed: true, storage: 200 },
        ]),
      ),
    ]).toEqual([])
  })

  it('keeps cyclic retentions closed, including self and repeated edges', () => {
    const problem = fixture([{ children: [0, 1, 1] }, { children: [0] }])
    expect([...immutableSelections(problem)]).toEqual([
      [true, true],
      [false, false],
    ])
  })

  it('restores older forward demands across repeated edges and backtracking', () => {
    const problem = fixture([
      { children: [3, 3] },
      { children: [3] },
      { storage: 203 },
      { storage: 203 },
    ])
    const masks = [...immutableSelections(problem)]
    expect(masks[0]).toEqual([true, true, false, true])
    expect(masks).toEqual(reference(problem))
    expect(new Set(masks).size).toBe(masks.length)
  })

  it('preserves the complete stream for two cycles competing for the same owners', () => {
    const size = 12
    const rows: Array<Partial<CompactImmutableInput['rows'][number]>> = [
      { children: [1, size + 1], storage: 999 },
    ]
    for (let copy = 0; copy < 2; copy += 1)
      for (let node = 0; node < size; node += 1)
        rows.push({
          children: [1 + copy * size + ((node + 1) % size)],
          storage: 200 + node,
        })
    const problem = fixture(rows)
    const masks = [...immutableSelections(problem)]
    expect(masks).toEqual([
      [false, ...new Array<boolean>(size).fill(true), ...new Array<boolean>(size).fill(false)],
      [false, ...new Array<boolean>(size).fill(false), ...new Array<boolean>(size).fill(true)],
      new Array<boolean>(2 * size + 1).fill(false),
    ])
    expect(masks).toEqual(reference(problem))
  })

  it('rejects malformed retained storage and child indices explicitly', () => {
    const missing = { ...fixture([{}]), storages: [] }
    expect(() => [...immutableSelections(missing)]).toThrow('has no storage')
    for (const child of [-1, 1, 0.5])
      expect(() => [...immutableSelections(fixture([{ children: [child] }]))]).toThrow(
        'has invalid child',
      )
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

  it('does not retain two distinct Vue wrappers sharing writable storage', () => {
    const raw = { n: 0 }
    const a = reactive(raw)
    const b = shallowReactive(raw)
    const current = { a, b }
    const result = produce(current, (draft) => draft)
    expect(result).not.toBe(current)
    expect(result.a).toBe(a)
    expect(result.b).not.toBe(b)
    expect(storageIdentity(result.a)).not.toBe(storageIdentity(result.b))
    expect(raw.n).toBe(0)
  })

  it('keeps unchanged settled Date identities', () => {
    const current = { date: new Date(7), n: 0 }
    expect(produce(current, (draft) => draft)).toBe(current)
  })
})
