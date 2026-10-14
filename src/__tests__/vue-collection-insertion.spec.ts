import { assert, describe, it } from 'vitest'
import { reactive, readonly, shallowReactive, shallowReadonly, watchSyncEffect } from 'vue'

import { produce, reconcile, ReconcileError } from '../index'

describe.each([
  ['produce', produce],
  [
    'produce + reconcile',
    <T, R>(current: T, recipe: (draft: T) => R): R => reconcile(current, produce(current, recipe)),
  ],
] as const)('%s Vue collection insertion', (name, apply) => {
  describe.each(['empty', 'clear', 'delete'] as const)('%s membership', (transition) => {
    it.each(['raw', 'wrapped', 'draft'] as const)('preserves %s key aliases and edits', (form) => {
      const key = { n: 0 }
      const other = { n: 9 }
      const current = reactive({
        key,
        map: new Map(
          transition === 'empty'
            ? [[other, 9]]
            : [
                [key, 1],
                [other, 9],
              ],
        ),
        other,
        set: new Set(transition === 'empty' ? [other] : [key, other]),
      })
      const originalOther = current.other
      const result = apply(current, (draft) => {
        if (transition === 'clear') {
          draft.map.clear()
          draft.set.clear()
          draft.map.set(other, 9)
          draft.set.add(other)
        } else if (transition === 'delete') {
          assert.isTrue(draft.map.delete(key))
          assert.isTrue(draft.set.delete(key))
        }
        const inserted = form === 'raw' ? key : form === 'wrapped' ? reactive(key) : draft.key
        draft.map.set(inserted, 2)
        draft.set.add(inserted)
        draft.key.n = 3
        assert.equal(draft.map.get(draft.key), 2)
        assert.isTrue(draft.set.has(draft.key))
        return draft
      })

      assert.equal(result.key.n, 3)
      assert.equal(result.map.get(result.key), 2)
      assert.isTrue(result.set.has(result.key))
      const keys = [...result.map.keys()]
      const members = [...result.set]
      assert.equal(keys.length, 2)
      assert.equal(members.length, 2)
      assert.equal(keys[0], result.other)
      assert.equal(keys[1], result.key)
      assert.equal(members[0], result.other)
      assert.equal(members[1], result.key)
      assert.equal(result.other, originalOther)
      if (name === 'produce + reconcile') {
        assert.equal(result, current)
      } else {
        assert.equal(key.n, 0)
        assert.equal(current.map.size, transition === 'empty' ? 1 : 2)
        assert.equal(current.set.size, transition === 'empty' ? 1 : 2)
        assert.equal(current.map.has(current.key), transition !== 'empty')
        assert.equal(current.set.has(current.key), transition !== 'empty')
        result.key.n = 4
        assert.equal(current.key.n, 0)
      }
    })
  })
})

it.each([
  ['reactive', reactive],
  ['readonly', readonly],
  ['readonly over reactive', (value: object) => readonly(reactive(value))],
] as const)('retains %s identities after clearing and restoring collections', (_name, wrap) => {
  const key = { n: 0 }
  // Wrap each collection and the key consistently, including layered wrappers.
  const current = {
    key: wrap(key),
    map: wrap(new Map([[key, 1]])) as Map<object, number>,
    set: wrap(new Set([key])) as Set<object>,
  }
  const result = produce(current, (draft) => {
    draft.map.clear()
    draft.set.clear()
    draft.map.set(key, 1)
    draft.set.add(key)
    return draft
  })
  assert.equal(result, current)
  assert.equal([...result.map.keys()][0], [...current.map.keys()][0])
  assert.equal([...result.set][0], [...current.set][0])
})

it.each([false, true])('separates shallow collection storage after undo = %s', (undo) => {
  const key = { n: 0 }
  const current = {
    key: shallowReactive(key),
    map: shallowReactive(new Map([[key, 1]])),
    set: shallowReactive(new Set([key])),
  }
  const result = produce(current, (draft) => {
    if (undo) {
      draft.map.clear()
      draft.set.clear()
      draft.map.set(key, 1)
      draft.set.add(key)
    }
    return draft
  })
  // Retaining the raw key, Map, and Set preserves three identities. Keeping
  // the earlier shallow key wrapper would unnecessarily replace all three.
  assert.notEqual(result.key, current.key)
  assert.equal(result.map, current.map)
  assert.equal(result.set, current.set)
  const resultKey = [...result.map.keys()][0]
  assert.equal([...result.set][0], resultKey)
  assert.equal(result.map.get(resultKey), 1)
  assert.equal(resultKey, key)
  result.key.n = 9
  assert.equal(resultKey.n, 0)
  assert.equal(key.n, 0)
  assert.equal([...current.map.keys()][0], key)
  assert.equal([...current.set][0], key)
})

it('shares inserted Map keys, values, Set members, and property drafts', () => {
  const key = { n: 0 }
  const current = reactive({ key, map: new Map<object, typeof key>(), set: new Set<object>() })
  const result = produce(current, (draft) => {
    draft.map.set(key, key)
    draft.set.add(key)
    assert.equal(draft.map.get(key), draft.key)
    draft.map.get(key)!.n = 3
    return draft
  })
  assert.equal(result.map.get(result.key), result.key)
  assert.equal([...result.map.keys()][0], result.key)
  assert.equal([...result.set][0], result.key)
  assert.equal(result.key.n, 3)
  assert.equal(key.n, 0)
  assert.equal(current.map.size, 0)
  assert.equal(current.set.size, 0)
})

it('preserves inserted root and collection cycles', () => {
  const raw = { map: new Map<object, object>(), n: 0, set: new Set<object>() }
  const current = reactive(raw)
  const result = produce(current, (draft) => {
    draft.map.set(raw, draft.map)
    draft.set.add(raw)
    draft.n = 1
    return draft
  })
  assert.equal([...result.map.keys()][0], result)
  assert.equal(result.map.get(result), result.map)
  assert.equal([...result.set][0], result)
  assert.equal(result.n, 1)
  assert.equal(current.n, 0)
  assert.equal(current.map.size, 0)
  assert.equal(current.set.size, 0)
})

it.each([
  ['reactive', shallowReactive],
  ['readonly', shallowReadonly],
] as const)('does not deeply wrap shallow %s collection insertions', (_name, wrap) => {
  const key = { n: 0 }
  const current = {
    key,
    map: wrap(new Map<object, number>()) as Map<object, number>,
    set: wrap(new Set<object>()) as Set<object>,
  }
  const result = produce(current, (draft) => {
    draft.map.set(key, 2)
    draft.set.add(key)
    draft.key.n = 3
    return draft
  })
  assert.equal([...result.map.keys()][0], result.key)
  assert.equal([...result.set][0], result.key)
  assert.equal(result.key.n, 3)
  assert.equal(key.n, 0)
})

describe.each([
  ['deep', reactive],
  ['shallow', shallowReactive],
] as const)('%s Vue Map key storage', (depth, wrap) => {
  it.each([
    ['reactive', reactive],
    ['readonly', readonly],
  ] as const)('normalizes a new %s key before exposing it', (_name, wrapKey) => {
    const raw = { n: 0 }
    const current = {
      key: depth === 'deep' ? reactive(raw) : raw,
      map: wrap(new Map<object, number>()),
    }
    const result = produce(current, (draft) => {
      draft.map.set(wrapKey(raw), 2)
      draft.key.n = 3
      return draft
    })
    assert.equal([...result.map.keys()][0], result.key)
    assert.equal(result.map.get(result.key), 2)
    assert.equal(result.key.n, 3)
    assert.equal(raw.n, 0)
  })
})

it('does not normalize away a Map key already stored as a readonly wrapper', () => {
  const key = readonly({ n: 0 })
  const current = { key, map: reactive(new Map([[key, 1]])) }
  const result = produce(current, (draft) => {
    draft.map.set(key, 2)
    return draft
  })
  assert.equal(result.map.size, 1)
  assert.equal([...result.map.keys()][0], result.key)
  assert.equal(result.map.get(result.key), 2)
  assert.equal(current.map.get(key), 1)
})

it('normalizes insertions without writes or observer notifications on the input', () => {
  const key = { n: 0 }
  const current = reactive({ key, map: new Map([[key, 1]]), set: new Set([key]) })
  const observations: number[][] = []
  const stop = watchSyncEffect(() => {
    observations.push([current.map.size, current.set.size, current.key.n])
  })
  try {
    const result = produce(current, (draft) => {
      draft.map.clear()
      draft.set.clear()
      draft.map.set(key, 2)
      draft.set.add(key)
      draft.key.n = 3
      return draft
    })
    assert.equal(result.map.get(result.key), 2)
    assert.isTrue(result.set.has(result.key))
    assert.deepEqual(observations, [[1, 1, 0]])
  } finally {
    stop()
  }
})

it.each(['throw', 'empty', 'wrong', 'extra'] as const)(
  'fails explicitly when an isolated wrapper iterator is %s',
  (mode) => {
    const key = { n: 0 }
    const backing = new Map<object, number>()
    const map = new Proxy(reactive(backing), {
      get(target, property, receiver) {
        if (property === 'keys') {
          return () => {
            if (mode === 'throw') throw new Error('Iterator failure')
            return new Set(mode === 'empty' ? [] : mode === 'wrong' ? [{}] : [key, {}]).keys()
          }
        }
        return Reflect.get(target, property, receiver) as unknown
      },
    })
    assert.throws(
      () =>
        produce({ map }, (draft) => {
          draft.map.set(key, 2)
          return draft
        }),
      mode === 'throw' ? Error : ReconcileError,
      mode === 'throw'
        ? 'Iterator failure'
        : 'Draft wrapper iterator did not expose the inserted value.',
    )
    assert.equal(backing.size, 0)
    assert.equal(key.n, 0)
  },
)

it('keeps raw and wrapped identities distinct in ordinary collections', () => {
  const raw = { n: 0 }
  const wrapped = reactive(raw)
  const current = {
    map: new Map<object, number>(),
    raw,
    set: new Set<object>(),
    wrapped,
  }
  const result = produce(current, (draft) => {
    draft.map.set(raw, 1)
    draft.map.set(wrapped, 2)
    draft.set.add(raw)
    draft.set.add(wrapped)
    draft.raw.n = 3
    return draft
  })
  assert.equal(result.map.size, 2)
  assert.equal(result.set.size, 2)
  assert.equal(result.map.get(result.raw), 1)
  assert.equal(result.map.get(result.wrapped), 2)
  assert.isTrue(result.set.has(result.raw))
  assert.isTrue(result.set.has(result.wrapped))
  assert.notEqual(result.raw, result.wrapped)
  assert.equal(result.raw.n, 3)
  assert.equal(result.wrapped.n, 0)
  assert.equal(raw.n, 0)
})
