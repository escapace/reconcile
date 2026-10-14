import { assert, describe, it } from 'vitest'
import { reactive } from 'vue'

import { produce, reconcile, snapshot } from '../index'

it('keeps raw Vue map keys usable across a copy and reinsertion', () => {
  const key = { value: 0 }
  const current = reactive(new Map<object | string, number>([[key, 1]]))
  const result = produce(current, (draft) => {
    draft.set('other', 3)
    assert.equal(draft.get(key), 1)
    assert.isTrue(draft.has(key))
    draft.set(key, 2)
    assert.equal(draft.size, 2)
    assert.equal(draft.get(key), 2)
    assert.isTrue(draft.delete(key))
    assert.isFalse(draft.has(key))
    assert.isFalse(draft.delete(key))
    draft.set(key, 4)
    assert.equal(draft.size, 2)
    return draft
  })
  assert.deepEqual([...result.values()], [3, 4])
  assert.deepEqual([...current.values()], [1])
})

it('deletes a raw Vue map key on the first write', () => {
  const key = { value: 0 }
  const current = reactive(new Map([[key, 1]]))
  const result = produce(current, (draft) => {
    assert.isTrue(draft.delete(key))
    assert.equal(draft.size, 0)
    return draft
  })
  assert.equal(result.size, 0)
  assert.equal(current.size, 1)
})

it('keeps raw Vue set members usable across a copy and reinsertion', () => {
  const key = { value: 0 }
  const current = reactive(new Set<object | string>([key]))
  const result = produce(current, (draft) => {
    draft.add('other')
    assert.isTrue(draft.has(key))
    draft.add(key)
    assert.equal(draft.size, 2)
    assert.isTrue(draft.delete(key))
    assert.isFalse(draft.has(key))
    assert.isFalse(draft.delete(key))
    draft.add(key)
    assert.equal(draft.size, 2)
    return draft
  })
  assert.equal(result.size, 2)
  assert.equal(current.size, 1)
})

it('deletes a raw Vue set member on the first write', () => {
  const key = { value: 0 }
  const current = reactive(new Set([key]))
  const result = produce(current, (draft) => {
    assert.isTrue(draft.delete(key))
    assert.equal(draft.size, 0)
    return draft
  })
  assert.equal(result.size, 0)
  assert.equal(current.size, 1)
})

const identity = <T extends object>(value: T): T => value

describe.each([
  ['plain', identity],
  ['Vue', reactive],
] as const)('%s raw overlap', (_name, wrap) => {
  it.each([false, true])(
    'preserves next values when swapping raw children with caller publication = %s',
    (usePublication) => {
      const raw = { left: { value: 1 }, right: { value: 2 } }
      const current = wrap(raw)
      const next = { left: raw.right, right: raw.left }
      const expected = snapshot(next)
      const result = usePublication
        ? reconcile(
            current,
            produce(current, () => next),
          )
        : reconcile(current, next)
      assert.equal(result, current)
      assert.deepEqual(snapshot(result), expected)
      assert.notEqual(result.left, result.right)
    },
  )

  it('captures a raw array before shrinking its wrapped root', () => {
    const raw: unknown[] = [1, 2]
    const current = wrap(raw)
    const result = reconcile(current, [raw])
    assert.equal(result, current)
    assert.deepEqual(snapshot(result), [[1, 2]])
    assert.notEqual(result[0], result)
  })
})

it('updates a raw Vue map key on the first write without duplicating it', () => {
  const key = { value: 0 }
  const oldValue = { value: 1 }
  const current = reactive(new Map([[key, oldValue]]))
  const result = produce(current, (draft) => {
    const held = draft.get(key)!
    draft.set(key, { value: 2 })
    assert.equal(draft.size, 1)
    assert.equal(draft.get(key)!.value, 2)
    held.value = 3
    assert.equal(draft.get(key)!.value, 2)
    return draft
  })
  assert.deepEqual([...result.values()], [{ value: 2 }])
  assert.equal(current.get(key)!.value, 1)
})

it('keeps raw and wrapped keys distinct in ordinary maps and sets', () => {
  const raw = { value: 0 }
  const wrapped = reactive(raw)
  const current = {
    map: new Map<object | string, number>([[wrapped, 1]]),
    set: new Set<object | string>([wrapped]),
  }
  const result = produce(current, (draft) => {
    draft.map.set('other', 3)
    draft.set.add('other')
    assert.isFalse(draft.map.has(raw))
    assert.isFalse(draft.set.has(raw))
    draft.map.set(raw, 2)
    draft.set.add(raw)
    assert.equal(draft.map.size, 3)
    assert.equal(draft.set.size, 3)
    assert.equal(draft.map.get(wrapped), 1)
    assert.equal(draft.map.get(raw), 2)
    return draft
  })
  assert.equal(result.map.size, 3)
  assert.equal(result.set.size, 3)
  assert.equal(current.map.size, 1)
  assert.equal(current.set.size, 1)
})
