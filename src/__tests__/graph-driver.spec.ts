import { assert, describe, expect, it } from 'vitest'
import { claimModes } from '../graph/claims'
import { execute } from '../graph/driver'
import type { Binding, Domains } from '../types'
import { retainedCapacityDomains } from './fixtures/retained-capacity'

const domains: Domains = [
  [
    { identity: 1, required: [], retained: true, storage: 1 },
    { identity: 2, required: [], retained: false, storage: 2 },
  ],
]
const binding = (choice: number): Binding => ({
  choice,
  construction: [],
  exposed: choice,
  fixed: false,
  mode: 0,
  palette: [0, 1, 2],
  storage: choice,
  writer: choice,
})

const capacityRejects = (bindings: readonly Binding[]): boolean =>
  bindings.reduce((sum, entry) => sum + Number((entry.choice as number) < 10), 0) > 3 ||
  bindings[1].choice === 1

describe('graph publication driver', () => {
  it.each(['publish', 'readback'])(
    'preserves capacity-conflict streams across transient %s failures and later calls',
    (boundary) => {
      const problem = retainedCapacityDomains()
      const prepared: number[][] = []
      const result = execute(problem, {
        prepare: (selection) => {
          prepared.push([...selection])
          return selection.map((choice, node) => binding(problem[node][choice].identity as number))
        },
        publish: (state) =>
          boundary === 'publish' && capacityRejects(state.bindings) ? { rejected: 2 } : true,
        readback: (state, node) =>
          boundary === 'readback' && node === 2 && capacityRejects(state.bindings)
            ? { kind: 'reject', node: 2 }
            : { kind: 'match' },
      })
      assert.equal(result.kind, 'accepted')
      assert.deepEqual(prepared, [
        [0, 0, 0, 1, 0],
        [0, 0, 1, 0, 0],
        [0, 0, 1, 1, 0],
        [0, 1, 1, 0, 0],
      ])
      const next: number[][] = []
      assert.equal(
        execute(problem, {
          prepare: (selection) => {
            next.push([...selection])
            return selection.map((choice, node) =>
              binding(problem[node][choice].identity as number),
            )
          },
          publish: () => true,
          readback: () => ({ kind: 'match' }),
        }).kind,
        'accepted',
      )
      assert.deepEqual(next, [[0, 0, 0, 1, 0]])
    },
  )
  it('advances rejected plans and never carries checks or claims to a replacement', () => {
    const starts: number[][] = []
    const planIds = new Set<number | object>()
    const result = execute(domains, {
      prepare: ([choice]) => [binding(domains[0][choice].identity as number)],
      publish: (state) => {
        planIds.add(state.id)
        starts.push([
          state.bindings[0].choice as number,
          state.revision,
          ...claimModes(state.claims[0]),
        ])
        return true
      },
      readback: (state) =>
        state.bindings[0].choice === 1
          ? { exposed: 10, kind: 'rebind', mode: 1, node: 0, storage: 1 }
          : { kind: 'match' },
    })
    expect(starts).toEqual([
      [1, 0, 0],
      [1, 1, 0, 1],
      [2, 0, 0],
    ])
    expect(planIds.size).toBe(2)
    expect(result.kind).toBe('accepted')
    assert(result.kind === 'accepted')
    expect(result.state.bindings[0].writer).toBe(2)
    expect(result.state.revision).toBe(0)
  })

  it('stops readback immediately after rebinding and checks every node in the new image', () => {
    const visited: number[][] = []
    const two: Domains = [
      domains[0].slice(0, 1),
      [{ identity: 3, required: [], retained: false, storage: 3 }],
    ]
    const result = execute(two, {
      prepare: () => [binding(1), binding(3)],
      publish: () => true,
      readback: (state, node) => {
        visited.push([state.revision, node])
        return state.revision < 2
          ? {
              exposed: 10 + state.revision,
              kind: 'rebind',
              mode: state.revision + 1,
              node: 0,
              storage: 1,
            }
          : { kind: 'match' }
      },
    })
    expect(visited).toEqual([
      [0, 0],
      [1, 0],
      [2, 0],
      [2, 1],
    ])
    expect(result.kind).toBe('accepted')
    assert(result.kind === 'accepted')
    expect(result.state.bindings[0].writer).toBe(1)
  })

  it('exhausts finite plans for explicit preparation, write and readback failures', () => {
    for (const failure of ['prepare', 'incomplete', 'publish', 'readback']) {
      let prepared = 0
      const result = execute(domains, {
        prepare: ([choice]) => {
          prepared += 1
          return failure === 'prepare'
            ? undefined
            : failure === 'incomplete'
              ? []
              : [binding(domains[0][choice].identity as number)]
        },
        publish: () => failure !== 'publish',
        readback: () => ({ kind: 'reject' }),
      })
      expect(result).toEqual({ kind: 'rejected' })
      expect(prepared).toBe(2)
    }
  })
  it('exhausts higher scores before using failure-informed fresh preferences', () => {
    const prepared: number[] = []
    const problem: Domains = [
      [
        { identity: 1, required: [], retained: true, storage: 1 },
        { identity: 2, required: [], retained: true, storage: 2 },
        { identity: 3, required: [], retained: false, storage: 3 },
      ],
    ]
    const result = execute(problem, {
      prepare: ([choice]) => {
        const identity = problem[0][choice].identity as number
        prepared.push(identity)
        return [binding(identity)]
      },
      publish: (state) => (state.bindings[0].choice === 1 ? { rejected: 0 } : true),
      readback: () => ({ kind: 'match' }),
    })
    expect(result.kind).toBe('accepted')
    expect(prepared).toEqual([1, 2])
  })
  it.each([false, true])(
    'revalidates provisional exposed retention before returning (replay fails: %s)',
    (failReplay) => {
      const problem: Domains = [
        [
          { identity: 1, required: [], retained: true, storage: 1 },
          { identity: 2, required: [], retained: true, storage: 2 },
          { identity: 3, required: [], retained: false, storage: 3 },
        ],
      ]
      const prepared: number[] = []
      const planIds = new Set<number | object>()
      let attempts = 0
      let reads = 0
      const result = execute(problem, {
        prepare: ([choice]) => {
          const identity = problem[0][choice].identity as number
          prepared.push(identity)
          return [binding(identity)]
        },
        publish: (state) => {
          planIds.add(state.id)
          if (state.bindings[0].choice === 1) {
            attempts += 1
            return !failReplay || attempts === 1
          }
          return state.bindings[0].choice === 3
        },
        readback: () => {
          reads += 1
          return { kind: 'match' }
        },
        retention: () => 0,
      })
      expect(result.kind).toBe('accepted')
      assert(result.kind === 'accepted')
      expect(result.state.bindings[0].choice).toBe(failReplay ? 3 : 1)
      expect(prepared).toEqual(failReplay ? [1, 2, 1, 3] : [1, 2, 1])
      expect(planIds.size).toBe(prepared.length)
      expect(reads).toBe(2)
    },
  )
  it('continues searching when replay falls below the remembered exposed score', () => {
    const problem: Domains = [
      domains[0],
      [
        { identity: 3, required: [], retained: true, storage: 3 },
        { identity: 4, required: [], retained: false, storage: 4 },
      ],
    ]
    const prepared: number[][] = []
    let observed = 0
    const result = execute(problem, {
      prepare(selection) {
        prepared.push([...selection])
        observed = prepared.length === 2 ? 0 : 1
        return selection.map((choice, node) => binding(problem[node][choice].identity as number))
      },
      publish: () => true,
      readback: () => ({ kind: 'match' }),
      retention: () => observed,
    })
    expect(result.kind).toBe('accepted')
    expect(prepared).toEqual([
      [0, 0],
      [0, 0],
      [0, 1],
    ])
  })
})
