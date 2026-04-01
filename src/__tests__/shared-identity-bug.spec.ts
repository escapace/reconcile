/**
 * Tests for the shared-identity bug fix in reconcile.
 *
 * BUG: When `current` and `next` share object identities at different positions,
 * reconcile's in-place mutations cascade through the shared references, corrupting data.
 *
 * FIX: Minimal snapshotting - snapshot shared next entries before reconciliation
 * to prevent cascading mutations while maintaining spec-conformant index/ordinal alignment.
 *
 * SPEC-CONFORMANT BEHAVIOR (per Lean spec):
 * - Alignment is by INDEX (arrays), ORDINAL (maps/sets), or KEY (objects)
 * - Result uses CURRENT identities
 * - Result has NEXT values (surface-equivalent to next)
 * - Objects ARE mutated to match next values
 *
 * Example: `current=[a,b]`, `next=[b,a]` where `a={id:'a'}` and `b={id:'b'}`.
 * After fix:
 * - `a.id = 'b'` (current[0] mutated to match next[0])
 * - `b.id = 'a'` (current[1] mutated to match next[1])
 * - `result = [a, b]` by identity
 * - result values = `[{id:'b'}, {id:'a'}]` (surface-eq to next)
 */

import { assert, describe, it } from 'vitest'
import { patch, createPatch, reconcile } from '../index'

// ============================================================================
// Set: Shared identity tests
// ============================================================================

describe('Set with shared object identities', () => {
  describe('reordering produces correct values without cascade corruption', () => {
    it('reordering Set entries swaps values correctly', () => {
      const a = { id: 'a', value: 100 }
      const b = { id: 'b', value: 200 }
      const c = { id: 'c', value: 300 }

      const original = new Set([a, b, c])

      // User reorders: [a, b, c] -> [c, a, b]
      const result = patch(original, (draft) => {
        draft.clear()
        draft.add(c)
        draft.add(a)
        draft.add(b)
        return draft
      })

      // Spec-conformant: current identities with next values
      // Position 0: a mutated to match c's original values
      // Position 1: b mutated to match a's original values
      // Position 2: c mutated to match b's original values
      assert.equal(a.id, 'c', "a should have c's id")
      assert.equal(a.value, 300, "a should have c's value")
      assert.equal(b.id, 'a', "b should have a's original id")
      assert.equal(b.value, 100, "b should have a's original value")
      assert.equal(c.id, 'b', "c should have b's original id")
      assert.equal(c.value, 200, "c should have b's original value")

      // Result has current identities in current order
      const resultArray = [...result]
      assert.equal(resultArray[0], a)
      assert.equal(resultArray[1], b)
      assert.equal(resultArray[2], c)

      // Result values match next order
      const resultIds = resultArray.map((x) => x.id)
      assert.deepEqual(resultIds, ['c', 'a', 'b'])
    })

    it('swapping two Set entries swaps values correctly', () => {
      const x = { name: 'x' }
      const y = { name: 'y' }

      const original = new Set([x, y])

      // Swap: [x, y] -> [y, x]
      const result = patch(original, (draft) => {
        draft.clear()
        draft.add(y)
        draft.add(x)
        return draft
      })

      // Spec-conformant: values are swapped
      assert.equal(x.name, 'y', "x should have y's name")
      assert.equal(y.name, 'x', "y should have x's original name")

      const resultArray = [...result]
      assert.equal(resultArray[0], x)
      assert.equal(resultArray[1], y)

      const resultNames = resultArray.map((v) => v.name)
      assert.deepEqual(resultNames, ['y', 'x'])
    })

    it('rotating Set entries rotates values correctly', () => {
      const items = [{ n: 1 }, { n: 2 }, { n: 3 }, { n: 4 }]
      const original = new Set(items)

      // Rotate left: [1,2,3,4] -> [2,3,4,1]
      const result = patch(original, (draft) => {
        draft.clear()
        draft.add(items[1])
        draft.add(items[2])
        draft.add(items[3])
        draft.add(items[0])
        return draft
      })

      // Spec-conformant: values are rotated into current positions
      assert.equal(items[0].n, 2, 'items[0] should have value 2')
      assert.equal(items[1].n, 3, 'items[1] should have value 3')
      assert.equal(items[2].n, 4, 'items[2] should have value 4')
      assert.equal(items[3].n, 1, 'items[3] should have value 1')

      const resultNs = [...result].map((v) => v.n)
      assert.deepEqual(resultNs, [2, 3, 4, 1])
    })
  })

  describe('direct reconcile() with shared objects', () => {
    it('reconcile swaps values correctly when current and next share objects', () => {
      const a = { id: 'a' }
      const b = { id: 'b' }

      const current = new Set([a, b])
      // eslint-disable-next-line perfectionist/sort-sets
      const next = new Set([b, a]) // Same objects, swapped order

      reconcile(current, next)

      // Spec-conformant: values swapped
      assert.equal(a.id, 'b', "a should have b's id")
      assert.equal(b.id, 'a', "b should have a's original id")
    })
  })
})

// ============================================================================
// Map: Shared identity tests
// ============================================================================

describe('Map with shared object identities', () => {
  describe('reordering produces correct values without cascade corruption', () => {
    it('reordering Map entries swaps keys and values correctly', () => {
      const k1 = { key: 'k1' }
      const k2 = { key: 'k2' }
      const v1 = { val: 'v1' }
      const v2 = { val: 'v2' }

      const original = new Map([
        [k1, v1],
        [k2, v2],
      ])

      // Reorder: [(k1,v1), (k2,v2)] -> [(k2,v2), (k1,v1)]
      const result = patch(original, (draft) => {
        draft.clear()
        draft.set(k2, v2)
        draft.set(k1, v1)
        return draft
      })

      // Spec-conformant: ordinal alignment swaps values
      // Position 0: k1 mutated to match k2, v1 mutated to match v2
      // Position 1: k2 mutated to match k1's original, v2 mutated to match v1's original
      assert.equal(k1.key, 'k2', "k1 should have k2's key")
      assert.equal(k2.key, 'k1', "k2 should have k1's original key")
      assert.equal(v1.val, 'v2', "v1 should have v2's val")
      assert.equal(v2.val, 'v1', "v2 should have v1's original val")

      // Result entries in order with swapped values
      const resultKeys = [...result.keys()].map((k) => k.key)
      const resultVals = [...result.values()].map((v) => v.val)
      assert.deepEqual(resultKeys, ['k2', 'k1'])
      assert.deepEqual(resultVals, ['v2', 'v1'])
    })

    it('swapping Map values swaps them correctly', () => {
      const v1 = { data: 'first' }
      const v2 = { data: 'second' }

      const original = new Map<string, typeof v1>([
        ['a', v1],
        ['b', v2],
      ])

      // Swap values: a->v1, b->v2 becomes a->v2, b->v1
      const result = patch(original, (draft) => {
        draft.set('a', v2)
        draft.set('b', v1)
        return draft
      })

      // Spec-conformant: v1 and v2 have swapped data
      assert.equal(v1.data, 'second', "v1 should have v2's data")
      assert.equal(v2.data, 'first', "v2 should have v1's original data")

      assert.equal(result.get('a')!.data, 'second')
      assert.equal(result.get('b')!.data, 'first')
    })

    it('swapping Map keys swaps them correctly', () => {
      const k1 = { id: 1 }
      const k2 = { id: 2 }

      const original = new Map<typeof k1, string>([
        [k1, 'first'],
        [k2, 'second'],
      ])

      // Swap key order: k1->"first", k2->"second" becomes k2->"first", k1->"second"
      const result = patch(original, (draft) => {
        draft.clear()
        draft.set(k2, 'first')
        draft.set(k1, 'second')
        return draft
      })

      // Spec-conformant: k1 and k2 have swapped ids
      assert.equal(k1.id, 2, "k1 should have k2's id")
      assert.equal(k2.id, 1, "k2 should have k1's original id")

      const entries = [...result.entries()]
      assert.equal(entries[0][0].id, 2)
      assert.equal(entries[1][0].id, 1)
    })
  })

  describe('direct reconcile() with shared objects', () => {
    it('reconcile swaps keys correctly when shared and reordered', () => {
      const k1 = { id: 'k1' }
      const k2 = { id: 'k2' }

      const current = new Map([
        [k1, 1],
        [k2, 2],
      ])
      /* eslint-disable perfectionist/sort-maps */
      const next = new Map([
        [k2, 2],
        [k1, 1],
      ])
      /* eslint-enable perfectionist/sort-maps */

      reconcile(current, next)

      assert.equal(k1.id, 'k2', "k1 should have k2's id")
      assert.equal(k2.id, 'k1', "k2 should have k1's original id")
    })

    it('reconcile swaps values correctly when shared and reordered', () => {
      const v1 = { data: 'v1' }
      const v2 = { data: 'v2' }

      const current = new Map([
        ['a', v1],
        ['b', v2],
      ])
      const next = new Map([
        ['a', v2],
        ['b', v1],
      ])

      reconcile(current, next)

      assert.equal(v1.data, 'v2', "v1 should have v2's data")
      assert.equal(v2.data, 'v1', "v2 should have v1's original data")
    })
  })
})

// ============================================================================
// Array: Shared identity tests
// ============================================================================

describe('Array with shared object identities', () => {
  describe('reordering produces correct values without cascade corruption', () => {
    it('reordering array elements swaps values correctly', () => {
      const a = { id: 'a' }
      const b = { id: 'b' }
      const c = { id: 'c' }

      const original = [a, b, c]

      // Reorder: [a, b, c] -> [c, a, b]
      const result = patch(original, (draft) => {
        draft[0] = c
        draft[1] = a
        draft[2] = b
        return draft
      })

      // Spec-conformant: values rotated into current positions
      assert.equal(a.id, 'c', "a should have c's id")
      assert.equal(b.id, 'a', "b should have a's original id")
      assert.equal(c.id, 'b', "c should have b's original id")

      // Result has current identities
      assert.equal(result[0], a)
      assert.equal(result[1], b)
      assert.equal(result[2], c)

      const resultIds = result.map((x) => x.id)
      assert.deepEqual(resultIds, ['c', 'a', 'b'])
    })

    it('swapping two array elements swaps values correctly', () => {
      const x = { value: 10 }
      const y = { value: 20 }

      const original = [x, y]

      // Swap: [x, y] -> [y, x]
      const result = patch(original, (draft) => {
        draft[0] = y
        draft[1] = x
        return draft
      })

      // Spec-conformant: values swapped
      assert.equal(x.value, 20, "x should have y's value")
      assert.equal(y.value, 10, "y should have x's original value")

      assert.equal(result[0], x)
      assert.equal(result[1], y)
      assert.equal(result[0].value, 20)
      assert.equal(result[1].value, 10)
    })

    it('reversing array reverses values correctly', () => {
      const items = [{ n: 1 }, { n: 2 }, { n: 3 }]
      const original = [...items]

      // Reverse: [1, 2, 3] -> [3, 2, 1]
      const result = patch(original, (draft) => {
        draft[0] = items[2]
        draft[1] = items[1]
        draft[2] = items[0]
        return draft
      })

      // Spec-conformant: values reversed into current positions
      assert.equal(items[0].n, 3, 'items[0] should have value 3')
      assert.equal(items[1].n, 2, 'items[1] should have value 2 (unchanged)')
      assert.equal(items[2].n, 1, 'items[2] should have value 1')

      const resultNs = result.map((v) => v.n)
      assert.deepEqual(resultNs, [3, 2, 1])
    })

    it('using splice to reorder swaps values correctly', () => {
      const a = { letter: 'a' }
      const b = { letter: 'b' }
      const c = { letter: 'c' }

      const original = [a, b, c]

      // Move last to first: [a, b, c] -> [c, a, b]
      const result = patch(original, (draft) => {
        const last = draft.pop()
        draft.unshift(last!)
        return draft
      })

      // Spec-conformant: values rotated
      assert.equal(a.letter, 'c', "a should have c's letter")
      assert.equal(b.letter, 'a', "b should have a's original letter")
      assert.equal(c.letter, 'b', "c should have b's original letter")

      const resultLetters = result.map((x) => x.letter)
      assert.deepEqual(resultLetters, ['c', 'a', 'b'])
    })
  })

  describe('direct reconcile() with shared objects', () => {
    it('reconcile swaps values correctly when elements are shared and reordered', () => {
      const a = { id: 'a' }
      const b = { id: 'b' }

      const current = [a, b]
      const next = [b, a]

      reconcile(current, next)

      assert.equal(a.id, 'b', "a should have b's id")
      assert.equal(b.id, 'a', "b should have a's original id")
    })
  })
})

// ============================================================================
// Plain object: Shared identity tests
// ============================================================================

describe('Plain object with shared object identities', () => {
  describe('swapping property values swaps them correctly', () => {
    it('swapping property values swaps them correctly', () => {
      const x = { name: 'x' }
      const y = { name: 'y' }

      const original = { first: x, second: y }

      // Swap: first->x, second->y becomes first->y, second->x
      const result = patch(original, (draft) => {
        draft.first = y
        draft.second = x
        return draft
      })

      // Spec-conformant: x and y have swapped names
      assert.equal(x.name, 'y', "x should have y's name")
      assert.equal(y.name, 'x', "y should have x's original name")

      assert.equal(result.first, x)
      assert.equal(result.second, y)
      assert.equal(result.first.name, 'y')
      assert.equal(result.second.name, 'x')
    })

    it('rotating property values rotates them correctly', () => {
      const a = { v: 'a' }
      const b = { v: 'b' }
      const c = { v: 'c' }

      const original = { p1: a, p2: b, p3: c }

      // Rotate: p1->a, p2->b, p3->c becomes p1->b, p2->c, p3->a
      const result = patch(original, (draft) => {
        draft.p1 = b
        draft.p2 = c
        draft.p3 = a
        return draft
      })

      // Spec-conformant: values rotated
      assert.equal(a.v, 'b', "a should have b's value")
      assert.equal(b.v, 'c', "b should have c's value")
      assert.equal(c.v, 'a', "c should have a's original value")

      assert.equal(result.p1.v, 'b')
      assert.equal(result.p2.v, 'c')
      assert.equal(result.p3.v, 'a')
    })

    it('swapping values AND changing key order works correctly', () => {
      const x = { id: 'x' }
      const y = { id: 'y' }

      const original = { a: x, b: y }

      // Change key order AND swap values: a->x, b->y becomes b->x, a->y
      const result = patch(original, (draft) => {
        delete (draft as Record<string, unknown>).a
        delete (draft as Record<string, unknown>).b
        ;(draft as Record<string, unknown>).b = x
        ;(draft as Record<string, unknown>).a = y
        return draft
      })

      // Spec-conformant: values swapped based on key alignment
      // Key 'a' in next has value y, key 'b' in next has value x
      // Current x (was at 'a') reconciled with next value at 'a' (y) -> x gets y's data
      // Current y (was at 'b') reconciled with next value at 'b' (x's original) -> y gets x's data

      // Key order should be [b, a]
      assert.deepEqual(Object.keys(result), ['b', 'a'])

      // The values are swapped according to key alignment
      assert.equal(result.b.id, 'x')
      assert.equal(result.a.id, 'y')
    })
  })

  describe('direct reconcile() with shared objects', () => {
    it('reconcile swaps values correctly when property values are shared and swapped', () => {
      const x = { id: 'x' }
      const y = { id: 'y' }

      const current = { a: x, b: y }
      const next = { a: y, b: x }

      reconcile(current, next)

      assert.equal(x.id, 'y', "x should have y's id")
      assert.equal(y.id, 'x', "y should have x's original id")
    })

    it('rebuilds nested reordered objects from a detached next source without re-planning children', () => {
      const xa = { id: 'xa' }
      const xb = { id: 'xb' }
      const yc = { id: 'yc' }
      const yd = { id: 'yd' }

      const x = { a: xa, b: xb }
      // eslint-disable-next-line perfectionist/sort-objects
      const y = { b: yc, a: yd }

      const current = { left: x, right: y }
      const next = { left: y, right: x }
      const result = reconcile(current, next) as {
        left: { a: { id: string }; b: { id: string } }
        right: { a: { id: string }; b: { id: string } }
      }

      assert.equal(result, current)
      assert.equal(result.left, x)
      assert.equal(result.right, y)
      assert.deepEqual(Object.keys(result.left), ['b', 'a'])
      assert.deepEqual(Object.keys(result.right), ['a', 'b'])
      assert.equal(result.left.b.id, 'yc')
      assert.equal(result.left.a.id, 'yd')
      assert.equal(result.right.a.id, 'xa')
      assert.equal(result.right.b.id, 'xb')
    })
  })
})

// ============================================================================
// Complex scenarios
// ============================================================================

describe('Complex shared identity scenarios', () => {
  it('nested structures with swapped wrappers swap values correctly', () => {
    const shared = { count: 0 }
    const wrapper1 = { id: 'w1', inner: shared }
    const wrapper2 = { id: 'w2', inner: shared }

    const original = { a: wrapper1, b: wrapper2 }

    // Swap the wrappers
    const result = patch(original, (draft) => {
      draft.a = wrapper2
      draft.b = wrapper1
      return draft
    })

    // Spec-conformant: wrapper ids swapped
    assert.equal(wrapper1.id, 'w2', "wrapper1 should have w2's id")
    assert.equal(wrapper2.id, 'w1', "wrapper2 should have w1's original id")

    // shared is inside both wrappers and referenced by both
    // After reconciliation, the inner references should still work
    assert.equal(result.a, wrapper1)
    assert.equal(result.b, wrapper2)
  })

  it('array with duplicate references and reordering handles correctly', () => {
    const a = { id: 'a' }
    const b = { id: 'b' }
    // Array has: [a, a, b]
    const original = [a, a, b]

    // Reorder to [b, a, a]
    const result = patch(original, (draft) => {
      draft[0] = b
      draft[1] = a
      draft[2] = a
      return draft
    })

    // Position 0: a[0] reconciled with b -> a gets b's values
    // Position 1: a[1] (same as a[0]) reconciled with a...
    // This is a complex case with duplicate refs
    // The first a is mutated, then when we try to reconcile the second a,
    // it's already been modified

    // Result should be surface-equivalent to next
    const resultIds = result.map((x) => x.id)
    assert.deepEqual(resultIds, ['b', 'a', 'a'])
  })

  it('swapping objects between different collection types', () => {
    const a = { id: 'a' }
    const b = { id: 'b' }

    const original = {
      array: [a, b],
      obj: { x: a, y: b },
    }

    // Swap in both collections
    const result = patch(original, (draft) => {
      draft.array[0] = b
      draft.array[1] = a
      draft.obj.x = b
      draft.obj.y = a
      return draft
    })

    // After reconciliation, values should be swapped
    // a and b are shared across both collections
    // The reconciliation order affects final values

    // Result should be surface-equivalent to next
    assert.equal(result.array[0].id, 'b')
    assert.equal(result.array[1].id, 'a')
    assert.equal(result.obj.x.id, 'b')
    assert.equal(result.obj.y.id, 'a')
  })

  it('deeply nested reorder swaps values correctly', () => {
    const a = { deep: { value: 'a' } }
    const b = { deep: { value: 'b' } }

    const original = {
      level1: {
        level2: {
          items: [a, b],
        },
      },
    }

    const result = patch(original, (draft) => {
      draft.level1.level2.items[0] = b
      draft.level1.level2.items[1] = a
      return draft
    })

    // Spec-conformant: values swapped at the deepest level
    assert.equal(a.deep.value, 'b', "a.deep.value should have b's value")
    assert.equal(b.deep.value, 'a', "b.deep.value should have a's original value")

    const items = result.level1.level2.items
    assert.equal(items[0].deep.value, 'b')
    assert.equal(items[1].deep.value, 'a')
  })

  it('cyclic structure with swapping handles cycles correctly', () => {
    interface Node {
      id: string
      next?: Node
    }

    const a: Node = { id: 'a' }
    const b: Node = { id: 'b' }
    a.next = b
    b.next = a

    const original = { first: a, second: b }

    const result = patch(original, (draft) => {
      draft.first = b
      draft.second = a
      return draft
    })

    // Spec-conformant: ids swapped, cycles preserved
    assert.equal(a.id, 'b', "a should have b's id")
    assert.equal(b.id, 'a', "b should have a's original id")

    // Cycles should still be intact (pointing to same objects)
    assert.equal(result.first, a)
    assert.equal(result.second, b)
  })
})

// ============================================================================
// createPatch + reconcile analysis
// ============================================================================

describe('createPatch produces shared identities - reconcile handles correctly', () => {
  it('createPatch output shares identities with current', () => {
    const a = { id: 'a' }
    const b = { id: 'b' }
    const current = new Set([a, b])

    const next = createPatch(current, (draft) => {
      draft.clear()
      draft.add(b)
      draft.add(a)
      return draft
    })

    // Verify next contains the same objects as current
    const nextArray = [...next]
    assert.equal(nextArray[0], b, 'next[0] should be b (same identity)')
    assert.equal(nextArray[1], a, 'next[1] should be a (same identity)')

    // After reconcile, values should be correctly swapped
    const result = reconcile(current, next)

    assert.equal(a.id, 'b', "a should have b's id after reconcile")
    assert.equal(b.id, 'a', "b should have a's original id after reconcile")

    // Result is surface-equivalent to next
    const resultIds = [...result].map((x) => x.id)
    assert.deepEqual(resultIds, ['b', 'a'])
  })

  it('demonstrates correct cascade-free reconciliation', () => {
    const a = { id: 'a' }
    const b = { id: 'b' }
    const c = { id: 'c' }

    const current = [a, b, c]
    const next = [c, a, b] // Same objects, different order

    // Before reconcile
    assert.equal(a.id, 'a')
    assert.equal(b.id, 'b')
    assert.equal(c.id, 'c')

    reconcile(current, next)

    // With fix: values are correctly swapped without cascade corruption
    // Position 0: a reconciled with snapshot(c) -> a.id = 'c'
    // Position 1: b reconciled with snapshot(a) -> b.id = 'a' (original)
    // Position 2: c reconciled with snapshot(b) -> c.id = 'b' (original)
    assert.equal(a.id, 'c', "a should have c's original id")
    assert.equal(b.id, 'a', "b should have a's original id")
    assert.equal(c.id, 'b', "c should have b's original id")

    // Without fix (cascade bug): a.id='c', b.id='c', c.id='c'
    // This test verifies the fix prevents the cascade
  })
})
