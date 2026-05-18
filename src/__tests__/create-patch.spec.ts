import { assert, describe, it } from 'vitest'

import { createPatch } from '../patch'
import { snapshot } from '../snapshot'

class UnsupportedCounter {
  value: number

  constructor(value: number) {
    this.value = value
  }
}

const firstSetEntry = <T>(value: Set<T>): T => value.values().next().value!
const firstMapEntry = <K, V>(value: Map<K, V>): readonly [K, V] => value.entries().next().value!
const returnedValue = () => 'ok'
const bytesOfArrayBuffer = (value: ArrayBufferLike): number[] => Array.from(new Uint8Array(value))
const bytesOfDataView = (value: DataView): number[] =>
  Array.from(new Uint8Array(value.buffer, value.byteOffset, value.byteLength))

interface Graph {
  touched: { count: number }
  child?: { parent: Graph }
}

interface Cyclic {
  nested: { count: number }
  self?: Cyclic
}

describe('createPatch', () => {
  it('returns a finalized next graph directly for draft-root mutations', () => {
    const current = {
      keep: { ok: true },
      list: [{ id: 1 }],
      nested: { count: 0 },
    }

    const result = createPatch(current, (draft) => {
      draft.list.push({ id: 2 })
      draft.nested.count = 1
      return draft
    })

    assert.notEqual(result, current)
    assert.equal(result.keep, current.keep)
    assert.notEqual(result.list, current.list)
    assert.notEqual(result.nested, current.nested)
    assert.deepEqual(result, {
      keep: { ok: true },
      list: [{ id: 1 }, { id: 2 }],
      nested: { count: 1 },
    })
    assert.deepEqual(current, {
      keep: { ok: true },
      list: [{ id: 1 }],
      nested: { count: 0 },
    })
  })

  it('returns a finalized nested draft proxy as the next root', () => {
    const current = {
      left: { count: 0 },
      right: { count: 0 },
    }

    const result = createPatch(current, (draft) => {
      draft.left.count = 3
      return draft.left
    })

    assert.deepEqual(result, { count: 3 })
    assert.deepEqual(current, {
      left: { count: 0 },
      right: { count: 0 },
    })
  })

  it('lets an unrelated non-draft return win over draft mutations', () => {
    const current = {
      nested: { count: 0 },
    }

    const result = createPatch(current, (draft) => {
      draft.nested.count = 5
      return { replace: true as const }
    })

    assert.deepEqual(result, { replace: true })
    assert.deepEqual(current, { nested: { count: 0 } })
  })

  it('treats undefined, primitive, and function returns as ordinary returned roots', () => {
    const current = { keep: true }

    assert.equal(
      createPatch<typeof current, undefined>(current, (_draft) => undefined),
      undefined,
    )
    assert.equal(
      createPatch(current, (_draft) => 1),
      1,
    )
    assert.equal(
      createPatch(current, (_draft) => 'patched'),
      'patched',
    )
    assert.equal(
      createPatch(current, (_draft) => returnedValue),
      returnedValue,
    )
    assert.deepEqual(current, { keep: true })
  })

  it('finalizes patch-owned drafts nested inside an ordinary returned root', () => {
    const current = {
      nested: { count: 0 },
    }

    const result = createPatch(current, (draft) => {
      draft.nested.count = 6
      return { wrapped: draft.nested }
    })

    assert.deepEqual(result, { wrapped: { count: 6 } })
    assert.deepEqual(current, { nested: { count: 0 } })
  })

  it('does not leak draft-side mutations to the live current graph during recipe execution', () => {
    const current = {
      nested: { count: 0 },
    }

    const result = createPatch(current, (draft) => {
      draft.nested.count = 1
      assert.equal(current.nested.count, 0)
      return draft
    })

    assert.equal(current.nested.count, 0)
    assert.equal(result.nested.count, 1)
  })

  it('can preserve untouched subtrees by reference into the finalized next graph', () => {
    const untouched = { keep: true }
    const current = {
      touched: { count: 0 },
      untouched,
    }

    const result = createPatch(current, (draft) => {
      draft.touched.count = 1
      return draft
    })

    assert.equal(result.untouched, untouched)
    assert.notEqual(result.touched, current.touched)
    assert.equal(current.touched.count, 0)
  })

  it('lets callers explicitly detach the returned next graph with snapshot(createPatch(...))', () => {
    const current = {
      touched: { count: 0 },
      untouched: { keep: true },
    }

    const next = createPatch(current, (draft) => {
      draft.touched.count = 1
      return draft
    })
    const detached = snapshot(next) as typeof next

    assert.notEqual(detached, next)
    assert.notEqual(detached.untouched, current.untouched)
    detached.untouched.keep = false
    assert.equal(current.untouched.keep, true)
    assert.equal(next.untouched.keep, true)
  })

  it('rebuilds an untouched subtree when reusing it would leave a back-reference into the previous root', () => {
    const current: Graph = {
      touched: { count: 0 },
    }
    current.child = { parent: current }

    const result = createPatch(current, (draft) => {
      draft.touched.count = 1
      return draft
    })

    assert.notEqual(result.child, current.child)
    assert.equal(result.child!.parent, result)
    assert.equal(current.child.parent, current)
    assert.equal(current.touched.count, 0)
    assert.equal(result.touched.count, 1)
  })

  it('preserves repeated references coherently in the returned next graph', () => {
    const shared = { count: 0 }
    const current = {
      left: shared,
      right: shared,
    }

    const result = createPatch(current, (draft) => {
      draft.left.count = 2
      return draft
    })

    assert.equal(result.left, result.right)
    assert.deepEqual(result.left, { count: 2 })
  })

  it('preserves closed untouched plain-object, array, map, and set subtrees by identity', () => {
    const untouchedObject = { keep: true }
    const untouchedArray = [{ id: 1 }]
    const untouchedKey = { key: true }
    const untouchedMap = new Map<object, { mapped: true }>([[untouchedKey, { mapped: true }]])
    const untouchedSetEntry = { set: true }
    const untouchedSet = new Set<object>([untouchedSetEntry])
    const current = {
      touched: { count: 0 },
      untouchedArray,
      untouchedMap,
      untouchedObject,
      untouchedSet,
    }

    const result = createPatch(current, (draft) => {
      draft.touched.count = 1
      return draft
    })

    assert.equal(result.untouchedObject, untouchedObject)
    assert.equal(result.untouchedArray, untouchedArray)
    assert.equal(result.untouchedMap, untouchedMap)
    assert.equal(result.untouchedSet, untouchedSet)
    assert.equal(firstMapEntry(result.untouchedMap)[0], untouchedKey)
    assert.equal(firstSetEntry(result.untouchedSet), untouchedSetEntry)
    assert.equal(current.touched.count, 0)
    assert.equal(result.touched.count, 1)
  })

  it('preserves closed repeated untouched references by identity and without collapse', () => {
    const shared = { keep: true }
    const current = {
      left: shared,
      right: shared,
      touched: { count: 0 },
    }

    const result = createPatch(current, (draft) => {
      draft.touched.count = 1
      return draft
    })

    assert.equal(result.left, shared)
    assert.equal(result.right, shared)
    assert.equal(result.left, result.right)
    assert.equal(current.touched.count, 0)
  })

  it('rebuilds an untouched plain object when it contains a reference into a touched subtree', () => {
    const touched = { count: 0 }
    const wrapper = { child: touched }
    const current = {
      touched,
      wrapper,
    }

    const result = createPatch(current, (draft) => {
      draft.touched.count = 2
      return draft
    })

    assert.notEqual(result.wrapper, wrapper)
    assert.equal(result.wrapper.child, result.touched)
    assert.notEqual(result.wrapper.child, current.touched)
    assert.equal(current.wrapper, wrapper)
    assert.equal(current.wrapper.child, current.touched)
  })

  it('rebuilds an untouched array when it contains a reference into a touched subtree', () => {
    const touched = { count: 0 }
    const list = [touched]
    const current = {
      list,
      touched,
    }

    const result = createPatch(current, (draft) => {
      draft.touched.count = 3
      return draft
    })

    assert.notEqual(result.list, list)
    assert.equal(result.list[0], result.touched)
    assert.notEqual(result.list[0], current.touched)
    assert.equal(current.list[0], current.touched)
  })

  it('rebuilds an untouched map when it contains a reference into a touched subtree, while preserving closed keys', () => {
    const touched = { count: 0 }
    const key = { id: 'stable-key' }
    const map = new Map<object, object>([[key, touched]])
    const current = {
      map,
      touched,
    }

    const result = createPatch(current, (draft) => {
      draft.touched.count = 4
      return draft
    })

    assert.notEqual(result.map, map)
    assert.equal(firstMapEntry(result.map)[0], key)
    assert.equal(firstMapEntry(result.map)[1], result.touched)
    assert.notEqual(firstMapEntry(result.map)[1], current.touched)
    assert.equal(firstMapEntry(current.map)[1], current.touched)
  })

  it('rebuilds an untouched set when it contains a reference into a touched subtree', () => {
    const touched = { count: 0 }
    const set = new Set<object>([touched])
    const current = {
      set,
      touched,
    }

    const result = createPatch(current, (draft) => {
      draft.touched.count = 5
      return draft
    })

    assert.notEqual(result.set, set)
    assert.equal(firstSetEntry(result.set), result.touched)
    assert.notEqual(firstSetEntry(result.set), current.touched)
    assert.equal(firstSetEntry(current.set), current.touched)
  })

  it('preserves closed current-backed children and rebuilds open current-backed children inside an ordinary returned root', () => {
    const closed = { keep: true }
    const touched = { count: 0 }
    const openWrapper = { child: touched }
    const current = {
      closed,
      openWrapper,
      touched,
    }

    const result = createPatch(current, (draft) => {
      draft.touched.count = 6

      return {
        closed,
        openWrapper,
        touched: draft.touched,
      }
    })

    assert.equal(result.closed, closed)
    assert.notEqual(result.openWrapper, openWrapper)
    assert.equal(result.openWrapper.child, result.touched)
    assert.notEqual(result.openWrapper.child, current.touched)
    assert.equal(current.openWrapper.child, current.touched)
    assert.deepEqual(result.touched, { count: 6 })
  })

  it('preserves moved draft-originating references at their final locations', () => {
    const current: {
      right: { count: number } | undefined
      left?: { count: number }
    } = {
      left: { count: 0 },
      right: undefined,
    }

    const result = createPatch(current, (draft) => {
      const moved = draft.left as { count: number }
      delete draft.left
      draft.right = moved
      draft.right.count = 4
      return draft
    }) as {
      right: { count: number }
      left?: { count: number }
    }

    assert.equal('left' in result, false)
    assert.deepEqual(result.right, { count: 4 })
    assert.deepEqual(current, { left: { count: 0 }, right: undefined })
  })

  it('finalizes one draft-originating value captured into arrays, maps, and sets', () => {
    const current = {
      item: { count: 0 },
      list: [] as Array<{ count: number }>,
      map: new Map<string, { count: number }>(),
      set: new Set<object>(),
    }

    const result = createPatch(current, (draft) => {
      draft.item.count = 15
      draft.list.push(draft.item)
      draft.map.set('item', draft.item)
      draft.set.add(draft.item)
      return draft
    })

    assert.equal(result.list[0], result.item)
    assert.equal(result.map.get('item'), result.item)
    assert.equal(firstSetEntry(result.set), result.item)
    assert.deepEqual(result.item, { count: 15 })
  })

  it('preserves self-references and cycles in the returned next graph', () => {
    const current: Cyclic = {
      nested: { count: 0 },
    }
    current.self = current

    const result = createPatch(current, (draft) => {
      draft.nested.count = 7
      return draft
    })

    assert.notEqual(result, current)
    assert.equal(result.self, result)
    assert.deepEqual(result.nested, { count: 7 })
    assert.equal(current.self, current)
    assert.equal(current.nested.count, 0)
  })

  it('allows a formerly shared path to diverge intentionally', () => {
    const shared = { count: 0 }
    const current = {
      left: shared,
      right: shared,
    }

    const result = createPatch(current, (draft) => {
      draft.left.count = 1
      draft.right = { count: 2 }
      return draft
    })

    assert.notEqual(result.left, result.right)
    assert.deepEqual(result.left, { count: 1 })
    assert.deepEqual(result.right, { count: 2 })
  })

  it('preserves plain-object key order and delete-vs-undefined behavior in the returned next graph', () => {
    const current: {
      bravo: number | undefined
      charlie: number
      alpha?: number
    } = {
      alpha: 1,
      bravo: 2,
      charlie: 3,
    }

    const result = createPatch(current, (draft) => {
      delete draft.alpha
      draft.bravo = undefined
      draft.alpha = 10
      return draft
    })

    assert.deepEqual(Reflect.ownKeys(result), ['bravo', 'charlie', 'alpha'])
    assert.equal('alpha' in result, true)
    assert.equal('bravo' in result, true)
    assert.equal(result.bravo, undefined)
    assert.deepEqual(result, {
      alpha: 10,
      bravo: undefined,
      charlie: 3,
    })
  })

  it('preserves array length, holes, and present undefined slots in the returned next graph', () => {
    const current = {
      list: [1, 2, 3] as Array<number | undefined>,
    }

    const result = createPatch(current, (draft) => {
      draft.list.length = 4
      Reflect.deleteProperty(draft.list, 1)
      draft.list[2] = undefined
      draft.list[3] = 4
      return draft
    })

    assert.equal(result.list.length, 4)
    assert.equal(1 in result.list, false)
    assert.equal(2 in result.list, true)
    assert.equal(result.list[2], undefined)
    assert.deepEqual(Object.keys(result.list), ['0', '2', '3'])
    assert.deepEqual(result.list, [1, undefined, undefined, 4])
  })

  it('supports indexed for loops over array drafts', () => {
    const current = {
      list: [{ count: 0 }, { count: 1 }, { count: 2 }],
    }

    const result = createPatch(current, (draft) => {
      for (let index = 0; index < draft.list.length; index += 1) {
        const item = draft.list[index]

        assert.notEqual(item, current.list[index])
        item.count += index + 1
      }

      return draft
    })

    assert.deepEqual(result.list, [{ count: 1 }, { count: 3 }, { count: 5 }])
    assert.deepEqual(current.list, [{ count: 0 }, { count: 1 }, { count: 2 }])
  })

  it('supports for...of iteration over array drafts', () => {
    const current = {
      list: [{ count: 0 }, { count: 1 }, { count: 2 }],
    }

    const result = createPatch(current, (draft) => {
      let index = 0

      for (const item of draft.list) {
        assert.notEqual(item, current.list[index])
        item.count += index + 2
        index += 1
      }

      assert.equal(index, draft.list.length)
      return draft
    })

    assert.deepEqual(result.list, [{ count: 2 }, { count: 4 }, { count: 6 }])
    assert.deepEqual(current.list, [{ count: 0 }, { count: 1 }, { count: 2 }])
  })

  it('supports Array.prototype.map over array drafts with draft elements', () => {
    const current = {
      list: [{ count: 0 }, { count: 1 }, { count: 2 }],
    }

    const result = createPatch(current, (draft) => {
      const mapped = draft.list.map((item, index) => {
        assert.notEqual(item, current.list[index])
        item.count += 10 + index
        return item.count
      })

      assert.deepEqual(mapped, [10, 12, 14])
      return draft
    })

    assert.deepEqual(result.list, [{ count: 10 }, { count: 12 }, { count: 14 }])
    assert.deepEqual(current.list, [{ count: 0 }, { count: 1 }, { count: 2 }])
  })

  it('supports Array.prototype.forEach over array drafts with draft elements', () => {
    const current = {
      list: [{ count: 0 }, { count: 1 }, { count: 2 }],
    }

    const result = createPatch(current, (draft) => {
      let total = 0

      draft.list.forEach((item, index) => {
        assert.notEqual(item, current.list[index])
        item.count += 20 + index
        total += item.count
      })

      assert.equal(total, 66)
      return draft
    })

    assert.deepEqual(result.list, [{ count: 20 }, { count: 22 }, { count: 24 }])
    assert.deepEqual(current.list, [{ count: 0 }, { count: 1 }, { count: 2 }])
  })

  it('supports array entries(), keys(), and values() over array drafts', () => {
    const current = {
      list: [{ count: 0 }, { count: 1 }, { count: 2 }],
    }

    const result = createPatch(current, (draft) => {
      assert.deepEqual(Array.from(draft.list.keys()), [0, 1, 2])

      const values = Array.from(draft.list.values())
      values.forEach((item, index) => {
        assert.notEqual(item, current.list[index])
      })

      const entries = Array.from(draft.list.entries())
      assert.deepEqual(
        entries.map(([index]) => index),
        [0, 1, 2],
      )

      entries.forEach(([index, item]) => {
        assert.equal(item, values[index])
        item.count += 30 + index
      })

      return draft
    })

    assert.deepEqual(result.list, [{ count: 30 }, { count: 32 }, { count: 34 }])
    assert.deepEqual(current.list, [{ count: 0 }, { count: 1 }, { count: 2 }])
  })

  it('preserves map order while finalizing draft-originating map keys coherently', () => {
    const key = { label: 'key' }
    const current = {
      key,
      map: new Map<object, number>([[key, 1]]),
    }

    const result = createPatch(current, (draft) => {
      draft.key.label = 'updated'
      assert.equal(current.key.label, 'key')
      assert.equal(draft.map.get(draft.key), 1)
      draft.map.delete(draft.key)
      draft.map.set(draft.key, 2)
      draft.map.set({ extra: true }, 3)
      return draft
    })

    const [firstKey] = firstMapEntry(result.map)

    assert.equal(firstKey, result.key)
    assert.notEqual(firstKey, current.key)
    assert.equal((firstKey as { label: string }).label, 'updated')
    assert.deepEqual(Array.from(result.map.values()), [2, 3])
    assert.equal(current.key.label, 'key')
  })

  it('finalizes draft-originating map keys when a nested draft map is the authoritative return', () => {
    const key = { label: 'key' }
    const current = {
      key,
      map: new Map<object, number>([[key, 1]]),
    }

    const result = createPatch(current, (draft) => {
      draft.key.label = 'updated'
      assert.equal(current.key.label, 'key')
      return draft.map
    })

    const [resultKey] = firstMapEntry(result)

    assert.notEqual(result, current.map)
    assert.notEqual(resultKey, current.key)
    assert.equal((resultKey as { label: string }).label, 'updated')
    assert.equal(result.get(resultKey), 1)
    assert.equal(result.get(current.key), undefined)
    assert.equal(current.key.label, 'key')
  })

  it('preserves final Map key iteration order at the createPatch boundary while finalizing draft-originating keys coherently', () => {
    const key = { label: 'key' }
    const trailingKey = { trailing: true }
    const current = {
      key,
      map: new Map<object, number>([
        [key, 1],
        [trailingKey, 9],
      ]),
    }

    const result = createPatch(current, (draft) => {
      draft.key.label = 'updated'
      draft.map.delete(draft.key)
      draft.map.set(draft.key, 2)
      draft.map.set({ extra: true }, 3)
      return draft
    })

    const resultKeys = Array.from(result.map.keys())

    assert.equal(resultKeys.length, 3)
    assert.equal(resultKeys[0], trailingKey)
    assert.equal(resultKeys[1], result.key)
    assert.notEqual(resultKeys[1], current.key)
    assert.equal((resultKeys[1] as { label: string }).label, 'updated')
    assert.deepEqual(Array.from(result.map.values()), [9, 2, 3])
  })

  it('finalizes draft-originating map keys nested inside an ordinary returned root', () => {
    const key = { label: 'key' }
    const current = {
      key,
      map: new Map<object, number>([[key, 1]]),
    }

    const result = createPatch(current, (draft) => {
      draft.key.label = 'updated'
      return {
        key: draft.key,
        map: draft.map,
      }
    })

    const [resultKey] = firstMapEntry(result.map)

    assert.equal(resultKey, result.key)
    assert.notEqual(result.key, current.key)
    assert.equal(result.key.label, 'updated')
    assert.equal(result.map.get(result.key), 1)
    assert.equal(result.map.get(current.key), undefined)
    assert.equal(current.key.label, 'key')
  })

  it('finalizes draft-originating Date map keys coherently', () => {
    const key = new Date('2024-01-01T00:00:00.000Z')
    const current = {
      key,
      map: new Map<Date, number>([[key, 1]]),
    }

    const result = createPatch(current, (draft) => {
      draft.key.setUTCFullYear(2025)
      assert.equal(current.key.getUTCFullYear(), 2024)
      draft.map.set(draft.key, 2)
      return draft
    })

    const [resultKey] = firstMapEntry(result.map)

    assert.equal(resultKey, result.key)
    assert.notEqual(resultKey, current.key)
    assert.equal(resultKey.getUTCFullYear(), 2025)
    assert.equal(result.map.get(result.key), 2)
    assert.equal(result.map.get(current.key), undefined)
    assert.equal(current.key.getUTCFullYear(), 2024)
  })

  it('finalizes draft-originating ArrayBuffer map keys coherently', () => {
    const key = new Uint8Array([1, 2, 3]).buffer
    const current = {
      key,
      map: new Map<ArrayBuffer, number>([[key, 1]]),
    }

    const result = createPatch(current, (draft) => {
      new Uint8Array(draft.key)[0] = 9
      assert.deepEqual(bytesOfArrayBuffer(current.key), [1, 2, 3])
      draft.map.set(draft.key, 2)
      return draft
    })

    const [resultKey] = firstMapEntry(result.map)

    assert.equal(resultKey, result.key)
    assert.notEqual(resultKey, current.key)
    assert.deepEqual(bytesOfArrayBuffer(resultKey), [9, 2, 3])
    assert.equal(result.map.get(result.key), 2)
    assert.equal(result.map.get(current.key), undefined)
    assert.deepEqual(bytesOfArrayBuffer(current.key), [1, 2, 3])
  })

  it('preserves set order and collection-local membership behavior', () => {
    const item = { count: 0 }
    const other = { keep: true }
    const current = {
      item,
      other,
      // eslint-disable-next-line perfectionist/sort-sets
      set: new Set<object>([other, item]),
    }

    const result = createPatch(current, (draft) => {
      assert.equal(draft.set.has(draft.item), true)
      draft.set.delete(draft.item)
      draft.item.count = 16
      draft.set.add(draft.item)
      return draft
    }) as {
      item: { count: number }
      other: { keep: true }
      set: Set<object>
    }

    assert.deepEqual(Array.from(result.set.values()), [result.other, result.item])
    assert.equal(result.set.has(result.item), true)
    assert.deepEqual(result.item, { count: 16 })
  })

  it('rejects iterator and callback iteration APIs on map and set drafts', () => {
    const current = {
      map: new Map<string, number>([['a', 1]]),
      set: new Set<number>([1]),
    }

    assert.throws(
      () =>
        createPatch(current, (draft) => {
          ;(draft.map as unknown as { entries: () => unknown }).entries()
          return draft
        }),
      TypeError,
      /not supported/,
    )

    assert.throws(
      () =>
        createPatch(current, (draft) => {
          ;(draft.set as unknown as { forEach: () => unknown }).forEach()
          return draft
        }),
      TypeError,
      /not supported/,
    )
  })

  it('preserves buffer and view alias coherence in the returned next graph', () => {
    const buffer = new Uint8Array([1, 2, 3, 4]).buffer
    const current = {
      buffer,
      typed: new Uint8Array(buffer),
      view: new DataView(buffer),
    }

    const result = createPatch(current, (draft) => {
      draft.typed[1] = 9
      return draft
    })

    assert.notEqual(result, current)
    assert.equal(result.typed.buffer, result.buffer)
    assert.equal(result.view.buffer, result.buffer)
    assert.deepEqual(Array.from(new Uint8Array(result.buffer)), [1, 9, 3, 4])
    assert.deepEqual(Array.from(new Uint8Array(current.buffer)), [1, 2, 3, 4])
  })

  it('preserves one coherent next-side buffer across mixed typed-array and DataView returned-next cases', () => {
    const current = {
      typed: new Uint8Array(new Uint8Array([9, 9, 9, 9]).buffer),
      view: new DataView(new Uint8Array([5, 6, 7, 8]).buffer),
    }

    const result = createPatch(current, (draft) => {
      draft.typed[1] = 10
      return {
        typed: new Uint16Array(draft.typed.buffer),
        view: new DataView(draft.typed.buffer, 1, 2),
      }
    }) as {
      typed: Uint16Array
      view: DataView
    }

    assert.equal(result.typed.buffer, result.view.buffer)
    assert.deepEqual(Array.from(new Uint8Array(result.typed.buffer)), [9, 10, 9, 9])
    assert.deepEqual(
      Array.from(
        new Uint8Array(result.view.buffer, result.view.byteOffset, result.view.byteLength),
      ),
      [10, 9],
    )
  })

  it('preserves ArrayBuffer and DataView aliasing in a finalized ordinary returned root', () => {
    const current = {
      touch: { count: 0 },
    }
    const nextBuffer = new Uint8Array([5, 6, 7, 8]).buffer

    const result = createPatch(current, (draft) => {
      draft.touch.count = 1
      return {
        buffer: nextBuffer,
        touch: draft.touch,
        view: new DataView(nextBuffer),
      }
    }) as {
      buffer: ArrayBuffer
      touch: { count: number }
      view: DataView
    }

    assert.equal(result.view.buffer, result.buffer)
    assert.deepEqual(bytesOfArrayBuffer(result.buffer), [5, 6, 7, 8])
    assert.deepEqual(bytesOfDataView(result.view), [5, 6, 7, 8])
    assert.equal(result.touch.count, 1)
    assert.equal(current.touch.count, 0)
  })

  it('preserves ArrayBuffer and DataView non-aliasing in a finalized ordinary returned root', () => {
    const current = {
      touch: { count: 0 },
    }

    const result = createPatch(current, (draft) => {
      draft.touch.count = 1
      return {
        buffer: new Uint8Array([5, 6, 7, 8]).buffer,
        touch: draft.touch,
        view: new DataView(new Uint8Array([9, 10, 11, 12]).buffer),
      }
    }) as {
      buffer: ArrayBuffer
      touch: { count: number }
      view: DataView
    }

    assert.notEqual(result.view.buffer, result.buffer)
    assert.deepEqual(bytesOfArrayBuffer(result.buffer), [5, 6, 7, 8])
    assert.deepEqual(bytesOfDataView(result.view), [9, 10, 11, 12])
  })

  it('preserves ArrayBuffer and typed-array aliasing in a finalized ordinary returned root', () => {
    const current = {
      touch: { count: 0 },
    }
    const nextBuffer = new Uint8Array([5, 6, 7, 8]).buffer

    const result = createPatch(current, (draft) => {
      draft.touch.count = 1
      return {
        buffer: nextBuffer,
        touch: draft.touch,
        typed: new Uint8Array(nextBuffer),
      }
    }) as {
      buffer: ArrayBuffer
      touch: { count: number }
      typed: Uint8Array
    }

    assert.equal(result.typed.buffer, result.buffer)
    assert.deepEqual(bytesOfArrayBuffer(result.buffer), [5, 6, 7, 8])
    assert.deepEqual(Array.from(result.typed), [5, 6, 7, 8])
  })

  it('preserves ArrayBuffer and typed-array non-aliasing in a finalized ordinary returned root', () => {
    const current = {
      touch: { count: 0 },
    }

    const result = createPatch(current, (draft) => {
      draft.touch.count = 1
      return {
        buffer: new Uint8Array([5, 6, 7, 8]).buffer,
        touch: draft.touch,
        typed: new Uint8Array(new Uint8Array([9, 10, 11, 12]).buffer),
      }
    }) as {
      buffer: ArrayBuffer
      touch: { count: number }
      typed: Uint8Array
    }

    assert.notEqual(result.typed.buffer, result.buffer)
    assert.deepEqual(bytesOfArrayBuffer(result.buffer), [5, 6, 7, 8])
    assert.deepEqual(Array.from(result.typed), [9, 10, 11, 12])
  })

  it('preserves DataView and typed-array aliasing in a finalized ordinary returned root', () => {
    const current = {
      touch: { count: 0 },
    }
    const nextBuffer = new Uint8Array([5, 6, 7, 8]).buffer

    const result = createPatch(current, (draft) => {
      draft.touch.count = 1
      return {
        touch: draft.touch,
        typed: new Uint8Array(nextBuffer),
        view: new DataView(nextBuffer),
      }
    }) as {
      touch: { count: number }
      typed: Uint8Array
      view: DataView
    }

    assert.equal(result.typed.buffer, result.view.buffer)
    assert.deepEqual(Array.from(result.typed), [5, 6, 7, 8])
    assert.deepEqual(bytesOfDataView(result.view), [5, 6, 7, 8])
  })

  it('preserves DataView and typed-array non-aliasing in a finalized ordinary returned root', () => {
    const current = {
      touch: { count: 0 },
    }

    const result = createPatch(current, (draft) => {
      draft.touch.count = 1
      return {
        touch: draft.touch,
        typed: new Uint8Array(new Uint8Array([5, 6, 7, 8]).buffer),
        view: new DataView(new Uint8Array([9, 10, 11, 12]).buffer),
      }
    }) as {
      touch: { count: number }
      typed: Uint8Array
      view: DataView
    }

    assert.notEqual(result.typed.buffer, result.view.buffer)
    assert.deepEqual(Array.from(result.typed), [5, 6, 7, 8])
    assert.deepEqual(bytesOfDataView(result.view), [9, 10, 11, 12])
  })

  it('preserves aliasing across multiple typed arrays that share one finalized next buffer', () => {
    const current = {
      touch: { count: 0 },
    }
    const nextBuffer = new Uint8Array([5, 6, 7, 8]).buffer

    const result = createPatch(current, (draft) => {
      draft.touch.count = 1
      return {
        left: new Uint8Array(nextBuffer, 0, 2),
        right: new Uint8Array(nextBuffer, 2, 2),
        touch: draft.touch,
      }
    }) as {
      left: Uint8Array
      right: Uint8Array
      touch: { count: number }
    }

    assert.equal(result.left.buffer, result.right.buffer)
    assert.deepEqual(Array.from(result.left), [5, 6])
    assert.deepEqual(Array.from(result.right), [7, 8])
  })

  it('preserves non-aliasing across typed arrays when a finalized ordinary returned root separates their buffers', () => {
    const current = {
      touch: { count: 0 },
    }

    const result = createPatch(current, (draft) => {
      draft.touch.count = 1
      return {
        left: new Uint8Array(new Uint8Array([5, 6]).buffer),
        right: new Uint8Array(new Uint8Array([7, 8]).buffer),
        touch: draft.touch,
      }
    }) as {
      left: Uint8Array
      right: Uint8Array
      touch: { count: number }
    }

    assert.notEqual(result.left.buffer, result.right.buffer)
    assert.deepEqual(Array.from(result.left), [5, 6])
    assert.deepEqual(Array.from(result.right), [7, 8])
  })

  it('preserves aliasing across multiple DataViews that share one finalized next buffer', () => {
    const current = {
      touch: { count: 0 },
    }
    const nextBuffer = new Uint8Array([5, 6, 7, 8]).buffer

    const result = createPatch(current, (draft) => {
      draft.touch.count = 1
      return {
        left: new DataView(nextBuffer, 0, 2),
        right: new DataView(nextBuffer, 2, 2),
        touch: draft.touch,
      }
    }) as {
      left: DataView
      right: DataView
      touch: { count: number }
    }

    assert.equal(result.left.buffer, result.right.buffer)
    assert.deepEqual(bytesOfDataView(result.left), [5, 6])
    assert.deepEqual(bytesOfDataView(result.right), [7, 8])
  })

  it('preserves non-aliasing across DataViews when a finalized ordinary returned root separates their buffers', () => {
    const current = {
      touch: { count: 0 },
    }

    const result = createPatch(current, (draft) => {
      draft.touch.count = 1
      return {
        left: new DataView(new Uint8Array([5, 6]).buffer),
        right: new DataView(new Uint8Array([7, 8]).buffer),
        touch: draft.touch,
      }
    }) as {
      left: DataView
      right: DataView
      touch: { count: number }
    }

    assert.notEqual(result.left.buffer, result.right.buffer)
    assert.deepEqual(bytesOfDataView(result.left), [5, 6])
    assert.deepEqual(bytesOfDataView(result.right), [7, 8])
  })

  it('preserves the full backing buffer for a finalized DataView with a larger aliased buffer', () => {
    const current = {
      touch: { count: 0 },
    }
    const nextBuffer = new Uint8Array([4, 5, 6, 7]).buffer

    const result = createPatch(current, (draft) => {
      draft.touch.count = 1
      return {
        touch: draft.touch,
        view: new DataView(nextBuffer, 1, 2),
      }
    }) as {
      touch: { count: number }
      view: DataView
    }

    assert.equal(result.view.byteOffset, 1)
    assert.equal(result.view.byteLength, 2)
    assert.equal(result.view.buffer.byteLength, 4)
    assert.deepEqual(bytesOfArrayBuffer(result.view.buffer), [4, 5, 6, 7])
    assert.deepEqual(bytesOfDataView(result.view), [5, 6])
  })

  it('reuses one finalized DataView when the same ordinary returned next DataView is referenced twice', () => {
    const current = {
      touch: { count: 0 },
    }
    const sharedNextView = new DataView(new Uint8Array([5, 6, 7, 8]).buffer, 1, 2)

    const result = createPatch(current, (draft) => {
      draft.touch.count = 1
      return {
        left: sharedNextView,
        right: sharedNextView,
        touch: draft.touch,
      }
    }) as {
      left: DataView
      right: DataView
      touch: { count: number }
    }

    assert.equal(result.left, result.right)
    assert.notEqual(result.left, sharedNextView)
    assert.equal(result.left.byteOffset, 1)
    assert.equal(result.left.byteLength, 2)
    assert.deepEqual(bytesOfArrayBuffer(result.left.buffer), [5, 6, 7, 8])
    assert.deepEqual(bytesOfDataView(result.left), [6, 7])
  })

  it('reuses one finalized typed-array view when the same ordinary returned next typed array is referenced twice', () => {
    const current = {
      touch: { count: 0 },
    }
    const sharedNextTyped = new Uint8Array(new Uint8Array([5, 6, 7, 8]).buffer, 1, 2)

    const result = createPatch(current, (draft) => {
      draft.touch.count = 1
      return {
        left: sharedNextTyped,
        right: sharedNextTyped,
        touch: draft.touch,
      }
    }) as {
      left: Uint8Array
      right: Uint8Array
      touch: { count: number }
    }

    assert.equal(result.left, result.right)
    assert.notEqual(result.left, sharedNextTyped)
    assert.equal(result.left.byteOffset, 1)
    assert.equal(result.left.byteLength, 2)
    assert.deepEqual(bytesOfArrayBuffer(result.left.buffer), [5, 6, 7, 8])
    assert.deepEqual(Array.from(result.left), [6, 7])
  })

  it('preserves typed-array byte offset changes in a finalized ordinary returned root', () => {
    const current = {
      touch: { count: 0 },
    }
    const nextBuffer = new Uint8Array([5, 6, 7, 8]).buffer

    const result = createPatch(current, (draft) => {
      draft.touch.count = 1
      return {
        touch: draft.touch,
        typed: new Uint8Array(nextBuffer, 1, 2),
      }
    }) as {
      touch: { count: number }
      typed: Uint8Array
    }

    assert.equal(result.typed.byteOffset, 1)
    assert.equal(result.typed.byteLength, 2)
    assert.deepEqual(bytesOfArrayBuffer(result.typed.buffer), [5, 6, 7, 8])
    assert.deepEqual(Array.from(result.typed), [6, 7])
  })

  it('preserves incompatible binary subtree replacements in a finalized ordinary returned root', () => {
    const current = {
      touch: { count: 0 },
    }

    const result = createPatch(current, (draft) => {
      draft.touch.count = 1
      return {
        buffer: new Uint8Array([5, 6, 7, 8]).buffer,
        touch: draft.touch,
        typed: new Uint16Array([9, 10]),
      }
    }) as {
      buffer: ArrayBuffer
      touch: { count: number }
      typed: Uint16Array | Uint8Array
    }

    assert.equal(result.typed.constructor, Uint16Array)
    assert.equal(result.buffer.byteLength, 4)
    assert.deepEqual(bytesOfArrayBuffer(result.buffer), [5, 6, 7, 8])
    assert.deepEqual(Array.from(result.typed), [9, 10])
  })

  it('preserves incompatible binary-view replacements when byte lengths change in a finalized ordinary returned root', () => {
    const current = {
      touch: { count: 0 },
    }

    const result = createPatch(current, (draft) => {
      draft.touch.count = 1
      return {
        touch: draft.touch,
        typed: new Uint8Array([5, 6, 7]),
        view: new DataView(new Uint8Array([8, 9, 10]).buffer),
      }
    }) as {
      touch: { count: number }
      typed: Uint8Array
      view: DataView
    }

    assert.equal(result.typed.constructor, Uint8Array)
    assert.equal(result.view.byteLength, 3)
    assert.deepEqual(Array.from(result.typed), [5, 6, 7])
    assert.deepEqual(bytesOfDataView(result.view), [8, 9, 10])
  })

  it('keeps representative unsupported/class fallback behavior best-effort rather than detached', () => {
    const current = {
      counter: new UnsupportedCounter(1),
      untouched: { keep: true },
    }

    const result = createPatch(current, (draft) => {
      draft.counter.value = 2
      return draft
    })

    assert.equal(result.counter instanceof UnsupportedCounter, true)
    assert.equal(result.counter.value, 2)
    assert.equal(current.counter.value, 1)
    assert.equal(result.untouched, current.untouched)
  })
})
