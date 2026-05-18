/**
 * Comprehensive semantic tests for `reconcile`.
 *
 * This file locks in the intended behavior of the `reconcile` operator as
 * specified in lean/README.md §§5-7 and proven in the Lean theorem layer
 * (ReconcileSpec.lean, ReconcileSoundness.lean).
 *
 * Test organization mirrors the specification structure:
 *   §5.1 - Witness invariants (observable through behavior)
 *   §5.2 - Root rule
 *   §5.3 - Recursive value rule
 *   §5.4 - Shared-object fast path
 *   §5.5 - Entry rule
 *   §6.x - Kind-specific rules
 *   §7.x - Surface equivalence and topology preservation
 *
 * Each test references the corresponding Lean theorem (R3-R14) where applicable.
 */

import { assert, describe, it } from 'vitest'
import { reconcile, snapshot } from '../index'

const returnFortyTwo = (): number => 42
const assertSameReference = (actual: unknown, expected: unknown): void => {
  assert.equal(actual, expected)
}
const assertNotSameReference = (actual: unknown, expected: unknown): void => {
  assert.notEqual(actual, expected)
}

// ============================================================================
// §5.2 — Root rule (ReconcileRootSpec)
// ============================================================================

describe('§5.2 Root rule', () => {
  describe('R4 — Root fast-path: SameValue equality returns current unchanged', () => {
    it('returns current for identical primitive values', () => {
      // SameValue(current, next) => return current
      assert.equal(reconcile(42, 42), 42)
      assert.equal(reconcile('hello', 'hello'), 'hello')
      assert.equal(reconcile(true, true), true)
      assert.equal(reconcile(null, null), null)
      assert.equal(reconcile(undefined, undefined), undefined)
    })

    it('returns current for identical object references', () => {
      const object = { x: 1 }
      const result = reconcile(object, object)
      assert.equal(result, object)
    })

    it('distinguishes +0 and -0 per SameValue semantics', () => {
      // Object.is(+0, -0) === false, so these are different values
      const result = reconcile(+0, -0)
      assert.equal(result, -0)
      assert.equal(Object.is(result, -0), true)
    })

    it('treats NaN as equal to NaN per SameValue semantics', () => {
      // Object.is(NaN, NaN) === true
      const result = reconcile(NaN, NaN)
      assert.equal(Number.isNaN(result), true)
    })
  })

  describe('R5 — Root replacement: returns next when types differ or mismatch', () => {
    it('returns next when current is primitive and next is object', () => {
      const next = { x: 1 }
      const result = reconcile(42, next)
      assert.equal(result, next)
    })

    it('returns next when current is object and next is primitive', () => {
      const current = { x: 1 }
      const result = reconcile(current, 'hello')
      assert.equal(result, 'hello')
    })

    it('returns next when both are primitives but different', () => {
      assert.equal(reconcile(42, 100), 100)
      assert.equal(reconcile('a', 'b'), 'b')
      assert.equal(reconcile(true, false), false)
    })

    it('returns next when object kinds differ (array vs plain object)', () => {
      const current = { 0: 'a', length: 1 }
      const next = ['a']
      const result = reconcile(current, next)
      assert.equal(result, next)
    })

    it('returns next when object kinds differ (Map vs plain object)', () => {
      const current = {}
      const next = new Map([['a', 1]])
      const result = reconcile(current, next)
      assert.equal(result, next)
    })

    it('returns next when object kinds differ (Set vs array)', () => {
      const current: unknown[] = []
      const next = new Set([1, 2])
      const result = reconcile(current, next)
      assert.equal(result, next)
    })

    it('returns next when object kinds differ (Date vs plain object)', () => {
      const current = { time: 0 }
      const next = new Date(0)
      const result = reconcile(current, next)
      assert.equal(result, next)
    })

    it('returns next when object kinds differ (ArrayBuffer vs plain object)', () => {
      const current = {}
      const next = new ArrayBuffer(8)
      const result = reconcile(current, next)
      assert.equal(result, next)
    })
  })

  describe('Root-vs-nested asymmetry', () => {
    it('root kind mismatch returns next directly (no snapshot)', () => {
      // At root, kind mismatch => return next, not snapshot(next)
      const next = { x: 1 }
      const result = reconcile(42, next)
      assert.equal(result, next) // Same identity
    })

    it('nested kind mismatch returns snapshot of next (not next directly)', () => {
      // At nested level, kind mismatch => snapshot(next)
      const nested = { x: 1 }
      const current = { child: 42 }
      const next = { child: nested }
      const result = reconcile(current, next)

      // Result child is surface-equivalent but different identity
      assert.notEqual(result.child, nested)
      assert.deepEqual(result.child, nested)
    })
  })
})

// ============================================================================
// §5.3 — Recursive value rule (ReconcileValueSpec)
// ============================================================================

describe('§5.3 Recursive value rule', () => {
  describe('R6 — Nested replacement via snapshot', () => {
    it('snapshots next when current child is primitive and next child is object', () => {
      const nested = { x: 1 }
      const current = { child: 42 }
      const next = { child: nested }
      const result = reconcile(current, next)

      assert.notEqual(result.child, nested)
      assert.deepEqual(result.child, nested)
    })

    it('snapshots next when current child is already consumed', () => {
      // When a current node has been consumed for one next node,
      // it cannot be reused for another. The second usage gets a snapshot.
      const shared = { count: 0 }
      const current = { a: shared, b: shared }

      // Create next where a and b point to different objects
      const nextA = { count: 1 }
      const nextB = { count: 2 }
      const next = { a: nextA, b: nextB }

      const result = reconcile(current, next)

      // 'a' consumes shared, 'b' must snapshot because shared is consumed
      assert.equal(result.a, shared)
      assert.equal(shared.count, 1)

      // 'b' is a snapshot (different identity from shared)
      assert.notEqual(result.b, shared)
      assert.equal(result.b.count, 2)
    })

    it('snapshots next when nested kinds differ', () => {
      const current = { child: [1, 2, 3] }
      const next = { child: { 0: 1, 1: 2, 2: 3 } }
      const result = reconcile(current, next) as { child: object }

      // Array vs plain object => snapshot
      assert.notEqual(result.child, next.child)
      assert.deepEqual(result.child, next.child)
    })
  })

  describe('Nested reuse when kind matches', () => {
    it('reuses current child when kinds match', () => {
      const currentChild = { x: 1 }
      const current = { child: currentChild }
      const next = { child: { x: 2 } }
      const result = reconcile(current, next)

      assert.equal(result.child, currentChild)
      assert.equal(currentChild.x, 2)
    })
  })
})

// ============================================================================
// §5.4 — Shared-object fast path (SharedObjectSpec)
// ============================================================================

describe('§5.4 Shared-object fast path', () => {
  describe('Equal current and next entries', () => {
    it('returns cached image when next is already mapped', () => {
      // If image(next) is defined, return image(next)
      const shared = { count: 0 }
      const current = { a: shared, b: shared }
      const next = { a: shared, b: shared } // Same object in next

      const result = reconcile(current, next) as { a: object; b: object }

      // Both paths see the same next object, should get same result
      assert.equal(result.a, result.b)
    })

    it('snapshots when current is already consumed for different next', () => {
      // reuse(current) != none AND image(next) == none => snapshot
      const shared = { count: 0 }
      const current = { a: shared, b: shared }

      // next.a is a different object, next.b is shared
      const nextA = { count: 5 }
      const next = { a: nextA, b: shared }

      const result = reconcile(current, next) as { a: object; b: object }

      // 'a' reconciles: shared consumed for nextA
      assert.equal(result.a, shared)
      assert.equal(shared.count, 5)

      // 'b' sees current=shared, next=shared
      // But shared was consumed for nextA (a different next node)
      // Per Lean spec §5.1: current can only be consumed for ONE next node
      // Since shared was consumed for nextA, and nextA !== shared, must snapshot
      assert.notEqual(result.b, shared)
      assert.equal((result.b as { count: number }).count, 5)
    })

    it('consumes current for next when both are fresh', () => {
      // reuse(current) == none AND image(next) == none => consume
      const shared = { count: 0 }
      const current = { a: shared }
      const next = { a: shared }

      const result = reconcile(current, next) as { a: object }

      // shared is consumed for shared, returns shared
      assert.equal(result.a, shared)
    })
  })

  describe('Witness invariant: current-node injectivity (R9)', () => {
    it('one current node serves at most one next node', () => {
      // Demonstrates the reuse injectivity invariant
      const shared = { count: 0 }
      const current = { a: shared, b: shared }
      const nextA = { count: 1 }
      const nextB = { count: 2 }
      const next = { a: nextA, b: nextB }

      const result = reconcile(current, next) as { a: object; b: object }

      // shared can only be consumed once
      // One of a or b gets shared, the other gets a snapshot
      const aIsShared = result.a === shared
      const bIsShared = result.b === shared

      assert.isTrue(aIsShared !== bIsShared, 'Exactly one should be shared')
    })
  })
})

// ============================================================================
// §5.5 — Entry rule (ReconcileEntrySpec)
// ============================================================================

describe('§5.5 Entry rule', () => {
  it('returns current for SameValue atoms', () => {
    const current = { x: 42 }
    const next = { x: 42 }
    const result = reconcile(current, next)
    assert.equal(result.x, 42)
  })

  it('delegates to shared-object rule for SameValue refs', () => {
    const shared = { nested: 1 }
    const current = { ref: shared }
    const next = { ref: shared }
    const result = reconcile(current, next) as { ref: object }
    assert.equal(result.ref, shared)
  })

  it('delegates to recursive rule for different values', () => {
    const current = { x: 1 }
    const next = { x: 2 }
    const result = reconcile(current, next)
    assert.equal(result.x, 2)
  })
})

// ============================================================================
// §6.1 — Array reconciliation
// ============================================================================

describe('§6.1 Arrays', () => {
  it('aligns by index, not by value matching', () => {
    // R11 — Canonical alignment: fixed by index
    const current = [1, 2, 3]
    const next = [3, 2, 1]
    const result = reconcile(current, next)

    assert.equal(result, current)
    assert.deepEqual(result, [3, 2, 1])
  })

  it('sets length to next length', () => {
    const current = [1, 2, 3, 4, 5]
    const next = [10, 20]
    const result = reconcile(current, next)

    assert.equal(result, current)
    assert.equal(result.length, 2)
    assert.deepEqual(result, [10, 20])
  })

  it('preserves holes exactly', () => {
    // eslint-disable-next-line no-sparse-arrays
    const current = [1, , 3]
    // eslint-disable-next-line no-sparse-arrays
    const next = [10, , 30]
    const result = reconcile(current, next)

    assert.equal(result, current)
    assert.equal(result.length, 3)
    assert.isFalse(1 in result) // Hole preserved
    assert.equal(result[0], 10)
    assert.equal(result[2], 30)
  })

  it('creates holes when next has holes', () => {
    const current = [1, 2, 3]
    // eslint-disable-next-line no-sparse-arrays
    const next = [10, , 30]
    const result = reconcile(current, next)

    assert.equal(result, current)
    assert.isFalse(1 in result)
  })

  it('fills holes when next has values', () => {
    // eslint-disable-next-line no-sparse-arrays
    const current = [1, , 3]
    const next = [10, 20, 30]
    const result = reconcile(current, next)

    assert.equal(result, current)
    assert.isTrue(1 in result)
    assert.equal(result[1], 20)
  })

  it('recursively reconciles element values', () => {
    const currentChild = { x: 1 }
    const current = [currentChild]
    const next = [{ x: 2 }]
    const result = reconcile(current, next) as [{ x: number }]

    assert.equal(result[0], currentChild)
    assert.equal(currentChild.x, 2)
  })

  it('ignores non-index own properties', () => {
    const current = [1, 2] as { extra?: string } & number[]
    current.extra = 'ignored'
    const next = [10, 20]
    const result = reconcile(current, next) as { extra?: string } & number[]

    assert.equal(result, current)
    assert.equal(result.extra, 'ignored') // Still there, not reconciled
  })
})

// ============================================================================
// §6.2 — Date reconciliation
// ============================================================================

describe('§6.2 Date', () => {
  it('mutates current date to next timestamp', () => {
    const current = new Date(1000)
    const next = new Date(2000)
    const result = reconcile(current, next)

    assert.equal(result, current)
    assert.equal(current.getTime(), 2000)
  })

  it('preserves date identity', () => {
    const current = new Date(0)
    const next = new Date(Date.UTC(2024, 0, 1))
    const result = reconcile(current, next)

    assert.equal(result, current)
  })
})

// ============================================================================
// §6.3 — Map reconciliation
// ============================================================================

describe('§6.3 Map', () => {
  describe('R14 — Ordinal alignment (not associative lookup)', () => {
    it('aligns by ordinal position, not by key matching', () => {
      const current = new Map([
        ['a', 1],
        ['b', 2],
      ])
      /* eslint-disable perfectionist/sort-maps */
      const next = new Map([
        ['b', 10],
        ['a', 20],
      ])
      /* eslint-enable perfectionist/sort-maps */
      const result = reconcile(current, next)

      assert.equal(result, current)
      // Position 0: current['a'] reconciled with next['b']
      // Position 1: current['b'] reconciled with next['a']
      // Keys are reconciled too, so order follows next
      assert.deepEqual(
        [...result.entries()],
        [
          ['b', 10],
          ['a', 20],
        ],
      )
    })

    it('preserves insertion order from next', () => {
      const current = new Map([
        ['x', 1],
        ['y', 2],
        ['z', 3],
      ])
      /* eslint-disable perfectionist/sort-maps */
      const next = new Map([
        ['z', 30],
        ['x', 10],
        ['y', 20],
      ])
      /* eslint-enable perfectionist/sort-maps */
      const result = reconcile(current, next)

      assert.deepEqual([...result.keys()], ['z', 'x', 'y'])
    })
  })

  it('recursively reconciles keys and values', () => {
    const currentKey = { id: 1 }
    const currentValue = { count: 0 }
    const current = new Map([[currentKey, currentValue]])

    const nextKey = { id: 2 }
    const nextValue = { count: 5 }
    const next = new Map([[nextKey, nextValue]])

    const result = reconcile(current, next)

    assert.equal(result, current)
    const [[resultKey, resultValue]] = [...result.entries()]
    assert.equal(resultKey, currentKey)
    assert.equal(resultKey.id, 2)
    assert.equal(resultValue, currentValue)
    assert.equal(resultValue.count, 5)
  })

  it('grows map when next is larger', () => {
    const current = new Map([['a', 1]])
    const next = new Map([
      ['a', 10],
      ['b', 20],
    ])
    const result = reconcile(current, next)

    assert.equal(result.size, 2)
  })

  it('shrinks map when next is smaller', () => {
    const current = new Map([
      ['a', 1],
      ['b', 2],
    ])
    const next = new Map([['x', 10]])
    const result = reconcile(current, next)

    assert.equal(result.size, 1)
  })

  it('returns current unchanged when all entries reconcile in place', () => {
    const current = new Map([
      ['a', 1],
      ['b', 2],
    ])
    const next = new Map([
      ['a', 1],
      ['b', 2],
    ])
    const result = reconcile(current, next)

    assert.equal(result, current)
  })
})

// ============================================================================
// §6.4 — Set reconciliation
// ============================================================================

describe('§6.4 Set', () => {
  describe('R14 — Ordinal alignment (not membership matching)', () => {
    it('aligns by ordinal position, not by membership', () => {
      const current = new Set([1, 2, 3])
      // eslint-disable-next-line perfectionist/sort-sets
      const next = new Set([30, 20, 10])
      const result = reconcile(current, next)

      assert.equal(result, current)
      // Position 0: 1 → 30, Position 1: 2 → 20, Position 2: 3 → 10
      assert.deepEqual([...result], [30, 20, 10])
    })

    it('preserves insertion order from next', () => {
      // For primitive values, ordinal reconciliation shows the order directly
      const current = new Set(['a', 'b', 'c'])
      // eslint-disable-next-line perfectionist/sort-sets
      const next = new Set(['c', 'a', 'b'])

      const result = reconcile(current, next)

      // Order follows next ordinal positions:
      // Position 0: 'a' ← 'c', Position 1: 'b' ← 'a', Position 2: 'c' ← 'b'
      assert.deepEqual([...result], ['c', 'a', 'b'])
    })
  })

  it('recursively reconciles values', () => {
    const currentValue = { count: 0 }
    const current = new Set([currentValue])
    const nextValue = { count: 5 }
    const next = new Set([nextValue])

    const result = reconcile(current, next)

    assert.equal(result, current)
    const [resultValue] = [...result]
    assert.equal(resultValue, currentValue)
    assert.equal(currentValue.count, 5)
  })

  it('grows set when next is larger', () => {
    const current = new Set([1])
    const next = new Set([10, 20])
    const result = reconcile(current, next)

    assert.equal(result.size, 2)
  })

  it('shrinks set when next is smaller', () => {
    const current = new Set([1, 2, 3])
    const next = new Set([10])
    const result = reconcile(current, next)

    assert.equal(result.size, 1)
  })

  it('returns current unchanged when all values reconcile in place', () => {
    const current = new Set([1, 2, 3])
    const next = new Set([1, 2, 3])
    const result = reconcile(current, next)

    assert.equal(result, current)
  })
})

// ============================================================================
// §6.5 — ArrayBuffer reconciliation
// ============================================================================

describe('§6.5 ArrayBuffer', () => {
  it('copies bytes in place when lengths match', () => {
    const current = new ArrayBuffer(4)
    const currentView = new Uint8Array(current)
    currentView.set([1, 2, 3, 4])

    const next = new ArrayBuffer(4)
    const nextView = new Uint8Array(next)
    nextView.set([10, 20, 30, 40])

    const result = reconcile(current, next)

    assert.equal(result, current)
    assert.deepEqual([...new Uint8Array(current)], [10, 20, 30, 40])
  })

  it('replaces buffer when lengths differ', () => {
    const current = new ArrayBuffer(4)
    const next = new ArrayBuffer(8)
    new Uint8Array(next).set([1, 2, 3, 4, 5, 6, 7, 8])

    const result = reconcile(current, next)

    assert.notEqual(result, current)
    assert.equal(result.byteLength, 8)
    assert.deepEqual([...new Uint8Array(result)], [1, 2, 3, 4, 5, 6, 7, 8])
  })
})

// ============================================================================
// §6.6 — DataView reconciliation
// ============================================================================

describe('§6.6 DataView', () => {
  it('reuses view when buffer and metadata match', () => {
    const currentBuffer = new ArrayBuffer(8)
    const current = new DataView(currentBuffer, 0, 4)

    const nextBuffer = new ArrayBuffer(8)
    new Uint8Array(nextBuffer).set([1, 2, 3, 4, 5, 6, 7, 8])
    const next = new DataView(nextBuffer, 0, 4)

    const result = reconcile(current, next)

    assert.equal(result, current)
    assert.equal(result.buffer, currentBuffer)
    assert.deepEqual([...new Uint8Array(currentBuffer)], [1, 2, 3, 4, 5, 6, 7, 8])
  })

  it('replaces view when offset differs', () => {
    const currentBuffer = new ArrayBuffer(8)
    const current = new DataView(currentBuffer, 0, 4)

    const nextBuffer = new ArrayBuffer(8)
    const next = new DataView(nextBuffer, 2, 4)

    const result = reconcile(current, next)

    assert.notEqual(result, current)
    assert.equal(result.byteOffset, 2)
    assert.equal(result.byteLength, 4)
  })

  it('replaces view when byte length differs', () => {
    const currentBuffer = new ArrayBuffer(8)
    const current = new DataView(currentBuffer, 0, 4)

    const nextBuffer = new ArrayBuffer(8)
    const next = new DataView(nextBuffer, 0, 6)

    const result = reconcile(current, next)

    assert.notEqual(result, current)
    assert.equal(result.byteLength, 6)
  })

  it('reconciles backing buffer recursively', () => {
    const currentBuffer = new ArrayBuffer(8)
    const current = new DataView(currentBuffer, 0, 4)

    const nextBuffer = new ArrayBuffer(8)
    new Uint8Array(nextBuffer).set([10, 20, 30, 40, 50, 60, 70, 80])
    const next = new DataView(nextBuffer, 0, 4)

    const result = reconcile(current, next)

    assert.equal(result.buffer, currentBuffer)
    assert.deepEqual([...new Uint8Array(currentBuffer)], [10, 20, 30, 40, 50, 60, 70, 80])
  })
})

// ============================================================================
// §6.7 — TypedArray reconciliation
// ============================================================================

describe('§6.7 TypedArray', () => {
  it('reuses view when buffer and metadata match', () => {
    const currentBuffer = new ArrayBuffer(8)
    const current = new Uint8Array(currentBuffer, 0, 4)
    current.set([1, 2, 3, 4])

    const nextBuffer = new ArrayBuffer(8)
    const next = new Uint8Array(nextBuffer, 0, 4)
    next.set([10, 20, 30, 40])

    const result = reconcile(current, next)

    assert.equal(result, current)
    assert.deepEqual([...current], [10, 20, 30, 40])
  })

  it('replaces view when constructor tag differs', () => {
    const currentBuffer = new ArrayBuffer(8)
    const current = new Uint8Array(currentBuffer)

    const nextBuffer = new ArrayBuffer(8)
    const next = new Int8Array(nextBuffer)

    const result = reconcile(current, next)

    // Different constructor tags => replacement
    assertNotSameReference(result, current)
    assert.instanceOf(result, Int8Array)
  })

  it('replaces view when offset differs', () => {
    const currentBuffer = new ArrayBuffer(8)
    const current = new Uint8Array(currentBuffer, 0, 4)

    const nextBuffer = new ArrayBuffer(8)
    const next = new Uint8Array(nextBuffer, 2, 4)

    const result = reconcile(current, next)

    assert.notEqual(result, current)
    assert.equal(result.byteOffset, 2)
  })

  it('replaces view when length differs', () => {
    const currentBuffer = new ArrayBuffer(8)
    const current = new Uint8Array(currentBuffer, 0, 4)

    const nextBuffer = new ArrayBuffer(8)
    const next = new Uint8Array(nextBuffer, 0, 6)

    const result = reconcile(current, next)

    assert.notEqual(result, current)
    assert.equal(result.length, 6)
  })

  it('reconciles backing buffer recursively', () => {
    const currentBuffer = new ArrayBuffer(8)
    const current = new Uint8Array(currentBuffer, 0, 4)

    const nextBuffer = new ArrayBuffer(8)
    new Uint8Array(nextBuffer).set([10, 20, 30, 40, 50, 60, 70, 80])
    const next = new Uint8Array(nextBuffer, 0, 4)

    const result = reconcile(current, next)

    assert.equal(result.buffer, currentBuffer)
    assert.deepEqual([...new Uint8Array(currentBuffer)], [10, 20, 30, 40, 50, 60, 70, 80])
  })

  describe('all typed array constructors', () => {
    const typedArrayConstructors = [
      Int8Array,
      Uint8Array,
      Uint8ClampedArray,
      Int16Array,
      Uint16Array,
      Int32Array,
      Uint32Array,
      Float32Array,
      Float64Array,
      BigInt64Array,
      BigUint64Array,
    ] as const

    for (const Ctor of typedArrayConstructors) {
      it(`reuses ${Ctor.name} when metadata matches`, () => {
        const current = new Ctor(4)
        const next = new Ctor(4)
        const result = reconcile(current, next)
        assert.equal(result, current)
      })
    }
  })
})

// ============================================================================
// §6.8 — Plain object reconciliation
// ============================================================================

describe('§6.8 Plain objects', () => {
  describe('R13 — Ordered-key publication', () => {
    it('result key order matches next key order exactly', () => {
      const current = { a: 1, b: 2, c: 3 }
      // eslint-disable-next-line perfectionist/sort-objects
      const next = { c: 30, a: 10, b: 20 }
      const result = reconcile(current, next) as Record<string, number>

      assert.equal(result, current)
      assert.deepEqual(Object.keys(result), ['c', 'a', 'b'])
    })

    it('preserves next key order across permutations', () => {
      const current = { x: 1, y: 2, z: 3 }
      // eslint-disable-next-line perfectionist/sort-objects
      const next = { z: 30, y: 20, x: 10 }
      const result = reconcile(current, next)

      assert.deepEqual(Object.keys(result), ['z', 'y', 'x'])
    })
  })

  describe('Aligned-key case', () => {
    it('updates values in place when keys align', () => {
      const current = { a: 1, b: 2 }
      const next = { a: 10, b: 20 }
      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.deepEqual(result, { a: 10, b: 20 })
    })

    it('deletes trailing current keys', () => {
      const current = { a: 1, b: 2, c: 3, d: 4 }
      const next = { a: 10, b: 20 }
      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.deepEqual(Object.keys(result), ['a', 'b'])
      assert.isFalse('c' in result)
      assert.isFalse('d' in result)
    })
  })

  describe('Rebuild case (key order divergence)', () => {
    it('rebuilds when first key differs', () => {
      const current = { a: 1, b: 2 }
      // eslint-disable-next-line perfectionist/sort-objects
      const next = { b: 20, a: 10 }
      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.deepEqual(Object.keys(result), ['b', 'a'])
    })

    it('rebuilds when a key is missing in next', () => {
      const current = { a: 1, b: 2, c: 3 }
      const next = { a: 10, c: 30 }
      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.deepEqual(Object.keys(result), ['a', 'c'])
      assert.isFalse('b' in result)
    })

    it('rebuilds when next has new keys', () => {
      const current = { a: 1 }
      const next = { a: 10, b: 20 }
      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.deepEqual(Object.keys(result), ['a', 'b'])
    })
  })

  describe('Symbol keys', () => {
    it('handles symbol keys in reconciliation', () => {
      const sym = Symbol('test')
      const current = { [sym]: 1 }
      const next = { [sym]: 10 }
      const result = reconcile(current, next) as { [key: symbol]: number }

      assert.equal(result, current)
      assert.equal(result[sym], 10)
    })

    it('preserves symbol key order from next', () => {
      const sym1 = Symbol('1')
      const sym2 = Symbol('2')
      const current = { [sym1]: 1, [sym2]: 2 }
      // eslint-disable-next-line perfectionist/sort-objects
      const next = { [sym2]: 20, [sym1]: 10 }
      const result = reconcile(current, next)

      assert.deepEqual(Object.getOwnPropertySymbols(result), [sym2, sym1])
    })
  })

  describe('Prototype handling', () => {
    it('retains current prototype (not next prototype)', () => {
      const proto1 = { inherited: 'from-current' }
      const proto2 = { inherited: 'from-next' }
      const current = Object.create(proto1, {
        x: { configurable: true, enumerable: true, value: 1, writable: true },
      }) as { x: number }
      const next = Object.create(proto2, {
        x: { configurable: true, enumerable: true, value: 10, writable: true },
      }) as { x: number }

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal(Object.getPrototypeOf(result), proto1)
      assert.equal(
        (Object.getPrototypeOf(result) as { inherited: string }).inherited,
        'from-current',
      )
    })
  })

  describe('Nested value reconciliation', () => {
    it('recursively reconciles nested objects', () => {
      const currentNested = { y: 1 }
      const current = { x: currentNested }
      const next = { x: { y: 10 } }
      const result = reconcile(current, next)

      assert.equal(result.x, currentNested)
      assert.equal(currentNested.y, 10)
    })
  })
})

// ============================================================================
// §7.1 — Surface equivalence (R3)
// ============================================================================

describe('§7.1 Surface equivalence (R3)', () => {
  it('result is surface-equivalent to next for plain objects', () => {
    const current = { a: 1, b: { c: 2 } }
    const next = { a: 10, b: { c: 20 }, d: 30 }
    const result = reconcile(current, next)

    assert.deepEqual(result, next)
  })

  it('result is surface-equivalent to next for arrays', () => {
    const current = [1, 2, 3]
    const next = [10, 20, 30, 40]
    const result = reconcile(current, next)

    assert.deepEqual(result, next)
  })

  it('result is surface-equivalent to next for maps', () => {
    const current = new Map([['a', 1]])
    const next = new Map([
      ['b', 2],
      ['c', 3],
    ])
    const result = reconcile(current, next)

    assert.deepEqual([...result], [...next])
  })

  it('result is surface-equivalent to next for sets', () => {
    const current = new Set([1])
    const next = new Set([2, 3, 4])
    const result = reconcile(current, next)

    assert.deepEqual([...result], [...next])
  })

  it('result is surface-equivalent to next for dates', () => {
    const current = new Date(0)
    const next = new Date(1000)
    const result = reconcile(current, next)

    assert.equal(result.getTime(), next.getTime())
  })

  it('result is surface-equivalent to next for array buffers', () => {
    const current = new ArrayBuffer(4)
    const next = new ArrayBuffer(4)
    new Uint8Array(next).set([1, 2, 3, 4])
    const result = reconcile(current, next)

    assert.deepEqual([...new Uint8Array(result)], [...new Uint8Array(next)])
  })
})

// ============================================================================
// §7.2 — Topology preservation
// ============================================================================

describe('§7.2 Topology preservation', () => {
  describe('T1/R7 — Sharing preservation', () => {
    it('equal next references produce equal result references', () => {
      const shared = { x: 1 }
      const current = { a: { x: 0 }, b: { x: 0 } }
      const next = { a: shared, b: shared }

      const result = reconcile(current, next) as { a: object; b: object }

      assert.equal(result.a, result.b)
    })

    it('preserves sharing through nested structures', () => {
      const shared = { x: 1 }
      const current = {
        level1: {
          level2a: { ref: { x: 0 } },
          level2b: { ref: { x: 0 } },
        },
      }
      const next = {
        level1: {
          level2a: { ref: shared },
          level2b: { ref: shared },
        },
      }

      const result = reconcile(current, next)

      assert.equal(result.level1.level2a.ref, result.level1.level2b.ref)
    })
  })

  describe('T2/R8 — No-collapse', () => {
    it('distinct next references produce distinct result references', () => {
      const nextA = { x: 1 }
      const nextB = { x: 1 } // Same value, different identity
      const shared = { x: 0 }
      const current = { a: shared, b: shared }
      const next = { a: nextA, b: nextB }

      const result = reconcile(current, next) as { a: object; b: object }

      assert.notEqual(result.a, result.b)
    })

    it('distinct next arrays produce distinct result arrays', () => {
      const nextA = [1, 2]
      const nextB = [1, 2]
      const current = { a: [0], b: [0] }
      const next = { a: nextA, b: nextB }

      const result = reconcile(current, next)

      assert.notEqual(result.a, result.b)
    })
  })

  describe('T3/R9 — Current-node injectivity', () => {
    it('a current node is consumed for at most one next node', () => {
      const shared = { count: 0 }
      const current = { a: shared, b: shared, c: shared }
      const nextA = { count: 1 }
      const nextB = { count: 2 }
      const nextC = { count: 3 }
      const next = { a: nextA, b: nextB, c: nextC }

      const result = reconcile(current, next) as { a: object; b: object; c: object }

      // Only one of a, b, c should be the original shared object
      const results = [result.a, result.b, result.c]
      const sharedCount = results.filter((r) => r === shared).length
      assert.equal(sharedCount, 1)
    })
  })

  describe('T4 — Cycle preservation', () => {
    it('preserves self-cycles', () => {
      interface Cyclic {
        value: number
        self?: Cyclic
      }
      const current: Cyclic = { value: 0 }
      current.self = current

      const next: Cyclic = { value: 10 }
      next.self = next

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal(result.self, result)
      assert.equal(result.value, 10)
    })

    it('preserves mutual cycles', () => {
      interface Node {
        value: number
        other?: Node
      }
      const currentA: Node = { value: 0 }
      const currentB: Node = { value: 0 }
      currentA.other = currentB
      currentB.other = currentA
      const current = { a: currentA, b: currentB }

      const nextA: Node = { value: 1 }
      const nextB: Node = { value: 2 }
      nextA.other = nextB
      nextB.other = nextA
      const next = { a: nextA, b: nextB }

      const result = reconcile(current, next)

      assert.equal(result.a.other, result.b)
      assert.equal(result.b.other, result.a)
    })

    it('preserves longer cycles', () => {
      interface Node {
        value: number
        next?: Node
      }
      const c1: Node = { value: 0 }
      const c2: Node = { value: 0 }
      const c3: Node = { value: 0 }
      c1.next = c2
      c2.next = c3
      c3.next = c1
      const current = { start: c1 }

      const n1: Node = { value: 1 }
      const n2: Node = { value: 2 }
      const n3: Node = { value: 3 }
      n1.next = n2
      n2.next = n3
      n3.next = n1
      const next = { start: n1 }

      const result = reconcile(current, next)

      assert.equal(result.start.next!.next!.next, result.start)
      assert.equal(result.start.value, 1)
      assert.equal(result.start.next!.value, 2)
      assert.equal(result.start.next!.next!.value, 3)
    })
  })

  describe('T5/R12 — Buffer/view alias preservation', () => {
    it('multiple DataViews sharing one next buffer share one result buffer', () => {
      const currentBuffer1 = new ArrayBuffer(8)
      const currentBuffer2 = new ArrayBuffer(8)
      const current = {
        view1: new DataView(currentBuffer1, 0, 4),
        view2: new DataView(currentBuffer2, 4, 4),
      }

      const nextBuffer = new ArrayBuffer(8)
      new Uint8Array(nextBuffer).set([1, 2, 3, 4, 5, 6, 7, 8])
      const next = {
        view1: new DataView(nextBuffer, 0, 4),
        view2: new DataView(nextBuffer, 4, 4),
      }

      const result = reconcile(current, next)

      assert.equal(result.view1.buffer, result.view2.buffer)
    })

    it('multiple TypedArrays sharing one next buffer share one result buffer', () => {
      const currentBuffer1 = new ArrayBuffer(8)
      const currentBuffer2 = new ArrayBuffer(8)
      const current = {
        arr1: new Uint8Array(currentBuffer1, 0, 4),
        arr2: new Uint8Array(currentBuffer2, 4, 4),
      }

      const nextBuffer = new ArrayBuffer(8)
      new Uint8Array(nextBuffer).set([1, 2, 3, 4, 5, 6, 7, 8])
      const next = {
        arr1: new Uint8Array(nextBuffer, 0, 4),
        arr2: new Uint8Array(nextBuffer, 4, 4),
      }

      const result = reconcile(current, next)

      assert.equal(result.arr1.buffer, result.arr2.buffer)
    })

    it('separate next buffers produce separate result buffers', () => {
      const currentBuffer = new ArrayBuffer(16)
      const current = {
        view1: new DataView(currentBuffer, 0, 8),
        view2: new DataView(currentBuffer, 8, 8),
      }

      const nextBuffer1 = new ArrayBuffer(8)
      const nextBuffer2 = new ArrayBuffer(8)
      const next = {
        view1: new DataView(nextBuffer1),
        view2: new DataView(nextBuffer2),
      }

      const result = reconcile(current, next)

      assert.notEqual(result.view1.buffer, result.view2.buffer)
    })
  })
})

// ============================================================================
// R10 — Locality of replacement
// ============================================================================

describe('R10 Locality of replacement', () => {
  it('replaces only incompatible child, not parent', () => {
    const currentChild = [1, 2, 3] // Array
    const current = { child: currentChild, sibling: { x: 1 } }
    const next = { child: { a: 1 }, sibling: { x: 2 } } // child: plain object (kind mismatch)

    const result = reconcile(current, next) as { child: object; sibling: { x: number } }

    // Parent is retained
    assert.equal(result, current)
    // Incompatible child is replaced (snapshot)
    assert.notEqual(result.child, currentChild)
    assert.notEqual(result.child, next.child)
    assert.deepEqual(result.child, next.child)
    // Compatible sibling is retained and reconciled
    assert.equal(result.sibling, current.sibling)
    assert.equal(result.sibling.x, 2)
  })

  it('replaces deeply nested incompatibility without affecting ancestors', () => {
    const deepArray = [1, 2]
    const current = {
      level1: {
        level2: {
          level3: deepArray,
        },
      },
    }
    const next = {
      level1: {
        level2: {
          level3: { converted: true },
        },
      },
    }

    const result = reconcile(current, next) as {
      level1: {
        level2: {
          level3: unknown
        }
      }
    }

    // All ancestor objects are retained
    assert.equal(result, current)
    assert.equal(result.level1, current.level1)
    assert.equal(result.level1.level2, current.level1.level2)
    // Only the incompatible leaf is replaced
    assert.notEqual(result.level1.level2.level3, deepArray)
    assert.deepEqual(result.level1.level2.level3, { converted: true })
  })
})

// ============================================================================
// R11 — Canonical alignment (no search-based matching)
// ============================================================================

describe('R11 Canonical alignment', () => {
  it('array alignment is by index, not by element equality', () => {
    const current = ['a', 'b', 'c']
    const next = ['c', 'b', 'a'] // Reverse order
    const result = reconcile(current, next)

    // Index 0: 'a' → 'c'
    // Index 1: 'b' → 'b'
    // Index 2: 'c' → 'a'
    assert.deepEqual(result, ['c', 'b', 'a'])
  })

  it('object alignment is by key identity, not by value equality', () => {
    const current = { x: 1, y: 2 }
    const next = { x: 2, y: 1 } // Values swapped
    const result = reconcile(current, next)

    // Key 'x': 1 → 2
    // Key 'y': 2 → 1
    assert.deepEqual(result, { x: 2, y: 1 })
  })

  it('map alignment is by ordinal, not by key lookup', () => {
    const current = new Map<string, number>([
      ['first', 100],
      ['second', 200],
    ])
    /* eslint-disable perfectionist/sort-maps */
    const next = new Map<string, number>([
      ['second', 20], // Would match 'second' by key, but aligns by ordinal
      ['first', 10],
    ])
    /* eslint-enable perfectionist/sort-maps */
    const result = reconcile(current, next)

    // Ordinal 0: ('first', 100) ← ('second', 20)
    // Ordinal 1: ('second', 200) ← ('first', 10)
    assert.deepEqual(
      [...result],
      [
        ['second', 20],
        ['first', 10],
      ],
    )
  })

  it('set alignment is by ordinal, not by membership', () => {
    const current = new Set([10, 20, 30])
    // eslint-disable-next-line perfectionist/sort-sets
    const next = new Set([30, 10, 20]) // Reordered
    const result = reconcile(current, next)

    // Ordinal alignment, not membership matching
    assert.deepEqual([...result], [30, 10, 20])
  })
})

// ============================================================================
// Edge cases and integration
// ============================================================================

describe('Edge cases', () => {
  describe('Empty containers', () => {
    it('handles empty to non-empty object', () => {
      const current = {}
      const next = { a: 1, b: 2 }
      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.deepEqual(result, next)
    })

    it('handles non-empty to empty object', () => {
      const current = { a: 1, b: 2 }
      const next = {}
      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.deepEqual(Object.keys(result), [])
    })

    it('handles empty to non-empty array', () => {
      const current: number[] = []
      const next = [1, 2, 3]
      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.deepEqual(result, next)
    })

    it('handles non-empty to empty array', () => {
      const current = [1, 2, 3]
      const next: number[] = []
      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal(result.length, 0)
    })

    it('handles empty to non-empty Map', () => {
      const current = new Map<string, number>()
      const next = new Map([['a', 1]])
      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal(result.size, 1)
    })

    it('handles non-empty to empty Map', () => {
      const current = new Map([['a', 1]])
      const next = new Map<string, number>()
      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal(result.size, 0)
    })

    it('handles empty to non-empty Set', () => {
      const current = new Set<number>()
      const next = new Set([1, 2])
      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal(result.size, 2)
    })

    it('handles non-empty to empty Set', () => {
      const current = new Set([1, 2])
      const next = new Set<number>()
      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal(result.size, 0)
    })
  })

  describe('null and undefined', () => {
    it('handles null as current', () => {
      const next = { x: 1 }
      const result = reconcile(null, next)
      assert.equal(result, next)
    })

    it('handles null as next', () => {
      const current = { x: 1 }
      const result = reconcile(current, null)
      assert.equal(result, null)
    })

    it('handles undefined as current', () => {
      const next = { x: 1 }
      const result = reconcile(undefined, next)
      assert.equal(result, next)
    })

    it('handles undefined as next', () => {
      const current = { x: 1 }
      const result = reconcile(current, undefined)
      assert.equal(result, undefined)
    })

    it('handles null values in objects', () => {
      const current = { x: { y: 1 } }
      const next = { x: null }
      const result = reconcile(current, next)

      assertSameReference(result, current)
      assert.equal(result.x, null)
    })
  })

  describe('Function values', () => {
    it('preserves functions by reference', () => {
      const current = { fn: (): number => 0 }
      const next = { fn: returnFortyTwo }
      const result = reconcile(current, next)

      assert.equal(result.fn, returnFortyTwo)
    })

    it('handles functions in snapshot replacements', () => {
      const current = { child: 'not-an-object' }
      const next = { child: { fn: returnFortyTwo } }
      const result = reconcile(current, next)

      // child is snapshotted, function preserved by reference
      assert.equal(result.child.fn, returnFortyTwo)
    })
  })

  describe('Mixed sharing scenarios', () => {
    it('handles diamond sharing pattern', () => {
      const shared = { value: 0 }
      const current = {
        left: { ref: { value: -1 } },
        right: { ref: { value: -1 } },
      }
      const next = {
        left: { ref: shared },
        right: { ref: shared },
      }

      const result = reconcile(current, next)

      assert.equal(result.left.ref, result.right.ref)
      assert.equal(result.left.ref.value, 0)
    })

    it('handles deep sharing with mutations', () => {
      const shared = { count: 10 }
      const current = {
        a: { deep: { ref: { count: 0 } } },
        b: { deep: { ref: { count: 0 } } },
      }
      const next = {
        a: { deep: { ref: shared } },
        b: { deep: { ref: shared } },
      }

      const result = reconcile(current, next)

      assert.equal(result.a.deep.ref, result.b.deep.ref)
      assert.equal(result.a.deep.ref.count, 10)
    })
  })
})

// ============================================================================
// Integration with snapshot
// ============================================================================

describe('Integration with snapshot', () => {
  it('snapshot followed by reconcile preserves structure', () => {
    const original = {
      array: [1, 2, 3],
      map: new Map([['a', 1]]),
      nested: { x: 1 },
    }

    const snapshotted = snapshot(original) as typeof original
    const modified = {
      ...snapshotted,
      array: [10, 20, 30],
      map: new Map([['b', 2]]),
      nested: { x: 10 },
    }

    const result = reconcile(original, modified)

    assert.equal(result, original)
    assert.equal(result.nested, original.nested)
    assert.equal(result.nested.x, 10)
  })

  it('reconcile result equals snapshot of next (surface equivalence)', () => {
    const current = { a: 1, b: { c: 2 } }
    const next = { a: 10, b: { c: 20, d: 30 }, e: 40 }

    const result = reconcile(current, next)
    const snapshotOfNext = snapshot(next)

    assert.deepEqual(result, snapshotOfNext)
  })
})
