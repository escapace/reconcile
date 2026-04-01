/**
 * createPatch-only coverage for the shared-identity reorder scenarios.
 *
 * Unlike reconcile, createPatch does not publish by mutating the current graph in place.
 * It returns a finalized next graph directly. These tests mirror the shared-identity reorder
 * scenarios and verify that finalization alone:
 *
 * - returns the expected next-side values in index/key/ordinal order,
 * - preserves intended sharing in the returned next graph, and
 * - does not leak cascade-style corruption back into current.
 */

import { assert, describe, it } from 'vitest'

import { createPatch } from '../index'

// ============================================================================
// Set: Shared identity tests
// ============================================================================

describe('createPatch with Set shared object identities', () => {
  describe('reordering produces the correct next graph', () => {
    it('reordering Set entries swaps values correctly', () => {
      const a = { id: 'a', value: 100 }
      const b = { id: 'b', value: 200 }
      const c = { id: 'c', value: 300 }

      const current = new Set([a, b, c])

      const result = createPatch(current, (draft) => {
        draft.clear()
        draft.add(c)
        draft.add(a)
        draft.add(b)
        return draft
      })

      const resultArray = [...result]
      assert.equal(resultArray[0], c)
      assert.equal(resultArray[1], a)
      assert.equal(resultArray[2], b)
      assert.deepEqual(
        resultArray.map((x) => x.id),
        ['c', 'a', 'b'],
      )
      assert.deepEqual(
        [...current].map((x) => x.id),
        ['a', 'b', 'c'],
      )
    })

    it('swapping two Set entries swaps values correctly', () => {
      const x = { name: 'x' }
      const y = { name: 'y' }

      const current = new Set([x, y])

      const result = createPatch(current, (draft) => {
        draft.clear()
        draft.add(y)
        draft.add(x)
        return draft
      })

      const resultArray = [...result]
      assert.equal(resultArray[0], y)
      assert.equal(resultArray[1], x)
      assert.deepEqual(
        resultArray.map((v) => v.name),
        ['y', 'x'],
      )
      assert.deepEqual(
        [...current].map((v) => v.name),
        ['x', 'y'],
      )
    })

    it('rotating Set entries rotates values correctly', () => {
      const items = [{ n: 1 }, { n: 2 }, { n: 3 }, { n: 4 }]
      const current = new Set(items)

      const result = createPatch(current, (draft) => {
        draft.clear()
        draft.add(items[1])
        draft.add(items[2])
        draft.add(items[3])
        draft.add(items[0])
        return draft
      })

      assert.deepEqual(
        [...result].map((v) => v.n),
        [2, 3, 4, 1],
      )
      assert.deepEqual(
        [...current].map((v) => v.n),
        [1, 2, 3, 4],
      )
    })
  })

  describe('sharing with current does not corrupt finalization', () => {
    it('createPatch swaps values correctly when the returned Set reuses current objects', () => {
      const a = { id: 'a' }
      const b = { id: 'b' }

      const current = new Set([a, b])

      const result = createPatch(current, (draft) => {
        draft.clear()
        draft.add(b)
        draft.add(a)
        return draft
      })

      const resultArray = [...result]
      assert.equal(resultArray[0], b)
      assert.equal(resultArray[1], a)
      assert.equal(a.id, 'a')
      assert.equal(b.id, 'b')
    })
  })
})

// ============================================================================
// Map: Shared identity tests
// ============================================================================

describe('createPatch with Map shared object identities', () => {
  describe('reordering produces the correct next graph', () => {
    it('reordering Map entries swaps keys and values correctly', () => {
      const k1 = { key: 'k1' }
      const k2 = { key: 'k2' }
      const v1 = { val: 'v1' }
      const v2 = { val: 'v2' }

      const current = new Map([
        [k1, v1],
        [k2, v2],
      ])

      const result = createPatch(current, (draft) => {
        draft.clear()
        draft.set(k2, v2)
        draft.set(k1, v1)
        return draft
      })

      const entries = [...result.entries()]
      assert.equal(entries[0][0], k2)
      assert.equal(entries[0][1], v2)
      assert.equal(entries[1][0], k1)
      assert.equal(entries[1][1], v1)
      assert.deepEqual(
        [...current.keys()].map((k) => k.key),
        ['k1', 'k2'],
      )
      assert.deepEqual(
        [...current.values()].map((v) => v.val),
        ['v1', 'v2'],
      )
    })

    it('swapping Map values swaps them correctly', () => {
      const v1 = { data: 'first' }
      const v2 = { data: 'second' }

      const current = new Map<string, typeof v1>([
        ['a', v1],
        ['b', v2],
      ])

      const result = createPatch(current, (draft) => {
        draft.set('a', v2)
        draft.set('b', v1)
        return draft
      })

      assert.equal(result.get('a'), v2)
      assert.equal(result.get('b'), v1)
      assert.equal(current.get('a'), v1)
      assert.equal(current.get('b'), v2)
      assert.equal(v1.data, 'first')
      assert.equal(v2.data, 'second')
    })

    it('swapping Map keys swaps them correctly', () => {
      const k1 = { id: 1 }
      const k2 = { id: 2 }

      const current = new Map<typeof k1, string>([
        [k1, 'first'],
        [k2, 'second'],
      ])

      const result = createPatch(current, (draft) => {
        draft.clear()
        draft.set(k2, 'first')
        draft.set(k1, 'second')
        return draft
      })

      const entries = [...result.entries()]
      assert.equal(entries[0][0], k2)
      assert.equal(entries[0][1], 'first')
      assert.equal(entries[1][0], k1)
      assert.equal(entries[1][1], 'second')
      assert.equal(k1.id, 1)
      assert.equal(k2.id, 2)
    })
  })

  describe('sharing with current does not corrupt finalization', () => {
    it('createPatch swaps keys correctly when shared and reordered', () => {
      const k1 = { id: 'k1' }
      const k2 = { id: 'k2' }

      const current = new Map([
        [k1, 1],
        [k2, 2],
      ])

      const result = createPatch(current, (draft) => {
        draft.clear()
        draft.set(k2, 2)
        draft.set(k1, 1)
        return draft
      })

      const resultKeys = [...result.keys()]
      assert.equal(resultKeys[0], k2)
      assert.equal(resultKeys[1], k1)
      assert.equal(k1.id, 'k1')
      assert.equal(k2.id, 'k2')
    })

    it('createPatch swaps values correctly when shared and reordered', () => {
      const v1 = { data: 'v1' }
      const v2 = { data: 'v2' }

      const current = new Map([
        ['a', v1],
        ['b', v2],
      ])

      const result = createPatch(current, (draft) => {
        draft.set('a', v2)
        draft.set('b', v1)
        return draft
      })

      assert.equal(result.get('a'), v2)
      assert.equal(result.get('b'), v1)
      assert.equal(v1.data, 'v1')
      assert.equal(v2.data, 'v2')
      assert.equal(current.get('a'), v1)
      assert.equal(current.get('b'), v2)
    })
  })
})

// ============================================================================
// Array: Shared identity tests
// ============================================================================

describe('createPatch with Array shared object identities', () => {
  describe('reordering produces the correct next graph', () => {
    it('reordering array elements swaps values correctly', () => {
      const a = { id: 'a' }
      const b = { id: 'b' }
      const c = { id: 'c' }

      const current = [a, b, c]

      const result = createPatch(current, (draft) => {
        draft[0] = c
        draft[1] = a
        draft[2] = b
        return draft
      })

      assert.equal(result[0], c)
      assert.equal(result[1], a)
      assert.equal(result[2], b)
      assert.deepEqual(
        result.map((x) => x.id),
        ['c', 'a', 'b'],
      )
      assert.deepEqual(
        current.map((x) => x.id),
        ['a', 'b', 'c'],
      )
    })

    it('swapping two array elements swaps values correctly', () => {
      const x = { value: 10 }
      const y = { value: 20 }

      const current = [x, y]

      const result = createPatch(current, (draft) => {
        draft[0] = y
        draft[1] = x
        return draft
      })

      assert.equal(result[0], y)
      assert.equal(result[1], x)
      assert.equal(result[0].value, 20)
      assert.equal(result[1].value, 10)
      assert.deepEqual(
        current.map((v) => v.value),
        [10, 20],
      )
    })

    it('reversing array reverses values correctly', () => {
      const items = [{ n: 1 }, { n: 2 }, { n: 3 }]
      const current = [...items]

      const result = createPatch(current, (draft) => {
        draft[0] = items[2]
        draft[1] = items[1]
        draft[2] = items[0]
        return draft
      })

      assert.deepEqual(
        result.map((v) => v.n),
        [3, 2, 1],
      )
      assert.deepEqual(
        current.map((v) => v.n),
        [1, 2, 3],
      )
    })

    it('using splice to reorder swaps values correctly', () => {
      const a = { letter: 'a' }
      const b = { letter: 'b' }
      const c = { letter: 'c' }

      const current = [a, b, c]

      const result = createPatch(current, (draft) => {
        const last = draft.pop()
        draft.unshift(last!)
        return draft
      })

      assert.deepEqual(
        result.map((x) => x.letter),
        ['c', 'a', 'b'],
      )
      assert.deepEqual(
        current.map((x) => x.letter),
        ['a', 'b', 'c'],
      )
    })
  })

  describe('sharing with current does not corrupt finalization', () => {
    it('createPatch swaps values correctly when elements are shared and reordered', () => {
      const a = { id: 'a' }
      const b = { id: 'b' }

      const current = [a, b]

      const result = createPatch(current, (draft) => {
        draft[0] = b
        draft[1] = a
        return draft
      })

      assert.equal(result[0], b)
      assert.equal(result[1], a)
      assert.equal(a.id, 'a')
      assert.equal(b.id, 'b')
    })
  })
})

// ============================================================================
// Plain object: Shared identity tests
// ============================================================================

describe('createPatch with plain-object shared identities', () => {
  describe('swapping property values produces the correct next graph', () => {
    it('swapping property values swaps them correctly', () => {
      const x = { name: 'x' }
      const y = { name: 'y' }

      const current = { first: x, second: y }

      const result = createPatch(current, (draft) => {
        draft.first = y
        draft.second = x
        return draft
      })

      assert.equal(result.first, y)
      assert.equal(result.second, x)
      assert.equal(x.name, 'x')
      assert.equal(y.name, 'y')
    })

    it('rotating property values rotates them correctly', () => {
      const a = { v: 'a' }
      const b = { v: 'b' }
      const c = { v: 'c' }

      const current = { p1: a, p2: b, p3: c }

      const result = createPatch(current, (draft) => {
        draft.p1 = b
        draft.p2 = c
        draft.p3 = a
        return draft
      })

      assert.equal(result.p1, b)
      assert.equal(result.p2, c)
      assert.equal(result.p3, a)
      assert.equal(a.v, 'a')
      assert.equal(b.v, 'b')
      assert.equal(c.v, 'c')
    })

    it('swapping values and changing key order works correctly', () => {
      const x = { id: 'x' }
      const y = { id: 'y' }

      const current = { a: x, b: y }

      const result = createPatch(current, (draft) => {
        delete (draft as Record<string, unknown>).a
        delete (draft as Record<string, unknown>).b
        ;(draft as Record<string, unknown>).b = x
        ;(draft as Record<string, unknown>).a = y
        return draft
      })

      assert.deepEqual(Object.keys(result), ['b', 'a'])
      assert.equal(result.b, x)
      assert.equal(result.a, y)
      assert.deepEqual(Object.keys(current), ['a', 'b'])
    })
  })

  describe('sharing with current does not corrupt finalization', () => {
    it('createPatch swaps values correctly when property values are shared and swapped', () => {
      const x = { id: 'x' }
      const y = { id: 'y' }

      const current = { a: x, b: y }

      const result = createPatch(current, (draft) => {
        draft.a = y
        draft.b = x
        return draft
      })

      assert.equal(result.a, y)
      assert.equal(result.b, x)
      assert.equal(x.id, 'x')
      assert.equal(y.id, 'y')
    })
  })
})

// ============================================================================
// Complex scenarios
// ============================================================================

describe('createPatch complex shared identity scenarios', () => {
  it('nested structures with swapped wrappers swap values correctly', () => {
    const shared = { count: 0 }
    const wrapper1 = { id: 'w1', inner: shared }
    const wrapper2 = { id: 'w2', inner: shared }

    const current = { a: wrapper1, b: wrapper2 }

    const result = createPatch(current, (draft) => {
      draft.a = wrapper2
      draft.b = wrapper1
      return draft
    })

    assert.equal(result.a, wrapper2)
    assert.equal(result.b, wrapper1)
    assert.equal(result.a.inner, shared)
    assert.equal(result.b.inner, shared)
    assert.equal(current.a, wrapper1)
    assert.equal(current.b, wrapper2)
  })

  it('array with duplicate references and reordering handles correctly', () => {
    const a = { id: 'a' }
    const b = { id: 'b' }

    const current = [a, a, b]

    const result = createPatch(current, (draft) => {
      draft[0] = b
      draft[1] = a
      draft[2] = a
      return draft
    })

    assert.equal(result[0], b)
    assert.equal(result[1], a)
    assert.equal(result[2], a)
    assert.equal(result[1], result[2])
    assert.deepEqual(
      result.map((x) => x.id),
      ['b', 'a', 'a'],
    )
    assert.deepEqual(
      current.map((x) => x.id),
      ['a', 'a', 'b'],
    )
  })

  it('swapping objects between different collection types', () => {
    const a = { id: 'a' }
    const b = { id: 'b' }

    const current = {
      array: [a, b],
      obj: { x: a, y: b },
    }

    const result = createPatch(current, (draft) => {
      draft.array[0] = b
      draft.array[1] = a
      draft.obj.x = b
      draft.obj.y = a
      return draft
    })

    assert.equal(result.array[0], b)
    assert.equal(result.array[1], a)
    assert.equal(result.obj.x, b)
    assert.equal(result.obj.y, a)
    assert.equal(result.array[0], result.obj.x)
    assert.equal(result.array[1], result.obj.y)
    assert.equal(current.array[0], a)
    assert.equal(current.array[1], b)
    assert.equal(current.obj.x, a)
    assert.equal(current.obj.y, b)
  })

  it('deeply nested reorder swaps values correctly', () => {
    const a = { deep: { value: 'a' } }
    const b = { deep: { value: 'b' } }

    const current = {
      level1: {
        level2: {
          items: [a, b],
        },
      },
    }

    const result = createPatch(current, (draft) => {
      draft.level1.level2.items[0] = b
      draft.level1.level2.items[1] = a
      return draft
    })

    const items = result.level1.level2.items
    assert.equal(items[0], b)
    assert.equal(items[1], a)
    assert.equal(items[0].deep.value, 'b')
    assert.equal(items[1].deep.value, 'a')
    assert.equal(current.level1.level2.items[0].deep.value, 'a')
    assert.equal(current.level1.level2.items[1].deep.value, 'b')
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

    const current = { first: a, second: b }

    const result = createPatch(current, (draft) => {
      draft.first = b
      draft.second = a
      return draft
    })

    assert.equal(result.first, b)
    assert.equal(result.second, a)
    assert.equal(result.first.next, a)
    assert.equal(result.second.next, b)
    assert.equal(current.first, a)
    assert.equal(current.second, b)
  })
})

// ============================================================================
// createPatch-only analysis
// ============================================================================

describe('createPatch shared-identity publication boundary', () => {
  it('createPatch output can share identities with current', () => {
    const a = { id: 'a' }
    const b = { id: 'b' }
    const current = new Set([a, b])

    const next = createPatch(current, (draft) => {
      draft.clear()
      draft.add(b)
      draft.add(a)
      return draft
    })

    const nextArray = [...next]
    assert.equal(nextArray[0], b)
    assert.equal(nextArray[1], a)
    assert.equal(a.id, 'a')
    assert.equal(b.id, 'b')
  })

  it('createPatch reordering does not cascade mutations into current', () => {
    const a = { id: 'a' }
    const b = { id: 'b' }
    const c = { id: 'c' }

    const current = [a, b, c]

    const next = createPatch(current, (draft) => {
      draft[0] = c
      draft[1] = a
      draft[2] = b
      return draft
    })

    assert.deepEqual(
      next.map((x) => x.id),
      ['c', 'a', 'b'],
    )
    assert.deepEqual(
      current.map((x) => x.id),
      ['a', 'b', 'c'],
    )
    assert.equal(next[0], c)
    assert.equal(next[1], a)
    assert.equal(next[2], b)
  })
})
