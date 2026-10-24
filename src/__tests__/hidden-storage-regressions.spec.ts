import { assert, describe, it } from 'vitest'
import { reactive } from 'vue'

import { produce, reconcile, snapshot } from '../index'

it('does not return a cached map value after deleting through an equivalent key', () => {
  const key = { value: 0 }
  const current = reactive(new Map([[key, { value: 1 }]]))
  const result = produce(current, (draft) => {
    const held = draft.get(key)!
    assert.isTrue(draft.delete(reactive(key)))
    assert.equal(draft.size, 0)
    assert.isFalse(draft.has(key))
    assert.isUndefined(draft.get(key))
    draft.set(reactive(key), { value: 2 })
    held.value = 3
    assert.equal(draft.get(key)!.value, 2)
    return draft
  })
  assert.deepEqual([...result.values()], [{ value: 2 }])
  assert.equal(current.get(key)!.value, 1)
})

describe.each([['Vue', reactive]] as const)('%s hidden current storage', (_name, wrap) => {
  it('preserves distinct next values despite shared current storage', () => {
    const raw = { value: 0 }
    const current = { left: raw, right: wrap(raw) }
    const next = { left: { value: 1 }, right: { value: 2 } }
    const result = reconcile(current, next)
    assert.deepEqual(snapshot(result), next)
    assert.notEqual(result.left, result.right)
    result.left.value = 3
    assert.equal(result.right.value, 2)
    assert.equal(next.left.value, 1)
  })
})

it('does not lose caller publication edits through a raw and Vue-wrapped sibling', () => {
  const raw = { value: 0 }
  const current = { left: raw, right: reactive(raw) }
  const result = reconcile(
    current,
    produce(current, (draft) => {
      draft.left.value = 1
      return draft
    }),
  )
  // A Vue proxy is a view of its raw object, so the change shows at both positions.
  assert.deepEqual(snapshot(result), { left: { value: 1 }, right: { value: 1 } })
  assert.equal(result.left, raw)
})

it.each([
  () => ({
    left: new Map([
      ['a', 1],
      ['b', 2],
    ]),
    raw: new Map([
      ['a', 0],
      ['b', 0],
    ]),
    right: new Map([
      ['a', 1],
      ['b', 2],
    ]),
  }),
  () => ({ left: new Set([1, 2]), raw: new Set([0]), right: new Set([1, 2]) }),
  () => ({ left: [1, 2], raw: [0, 0], right: [2] }),
  () => ({ left: new Array<unknown>(2), raw: [0, 0], right: [undefined, undefined] }),
  () => ({
    left: Object.fromEntries([
      ['a', 1],
      ['b', 2],
    ]),
    raw: { a: 0, b: 0 },
    right: Object.fromEntries([
      ['b', 2],
      ['a', 1],
    ]),
  }),
])('preserves order and shape despite hidden collection storage', (fixture) => {
  const { left, raw, right } = fixture()
  const next = { left, right }
  const result = reconcile({ left: raw, right: reactive(raw) }, next)
  assert.deepEqual(snapshot(result), next)
  if (result.left instanceof Map && left instanceof Map) {
    assert.deepEqual([...result.left], [...left])
  } else if (result.left instanceof Set && left instanceof Set) {
    assert.deepEqual([...result.left], [...left])
  } else {
    assert.deepEqual(Reflect.ownKeys(result.left), Reflect.ownKeys(left))
  }
})

it('preserves cycles and repeated references when replacing a conflicting result', () => {
  const raw = { value: 0 }
  const current: Record<string, unknown> = { left: raw, right: reactive(raw) }
  current.self = current
  const left = { value: 1 }
  const next: Record<string, unknown> = { alias: left, left, right: { value: 2 } }
  next.self = next
  const result = reconcile(current, next)
  assert.equal(result.self, result)
  assert.equal(result.alias, result.left)
  assert.notEqual(result.left, result.right)
  assert.deepEqual(result.left, { value: 1 })
  assert.deepEqual(result.right, { value: 2 })
  assert.notEqual(result, next)
})
