import { assert, it } from 'vitest'

import { reconcile, produce } from '../index'

it.each([false, true])('isolates inherited objects with reordered keys = %s', (reorder) => {
  const key = Symbol('item')
  const shared = { value: 1 }
  const prototype = { item: shared, [key]: shared }
  const current = Object.create(prototype) as {
    item: { value: number }
    [key]: { value: number }
    old?: number
  }
  const sibling = Object.create(prototype) as typeof current
  if (reorder) current.old = 0
  const nextShared = { value: 2 }
  const next = { item: nextShared, [key]: nextShared }
  const result = reconcile(current, next)

  assert.equal(result, current)
  assert.equal(Object.getPrototypeOf(result), prototype)
  assert.isTrue(Object.hasOwn(result, 'item'))
  assert.isTrue(Object.hasOwn(result, key))
  assert.equal(result.item, result[key])
  assert.notEqual(result.item, shared)
  assert.equal(result.item.value, 2)
  assert.equal(prototype.item.value, 1)
  assert.equal(sibling.item, shared)
  assert.equal(sibling.item.value, 1)
  assert.deepEqual(Reflect.ownKeys(result), Reflect.ownKeys(next))
})

it('does not mutate an inherited collection when applying a replacement caller publication', () => {
  const inherited = new Map([['old', { value: 1 }]])
  const prototype = { items: inherited }
  const current = Object.create(prototype) as typeof prototype
  const result = reconcile(
    current,
    produce(current, () => ({ items: new Map([['new', { value: 2 }]]) })),
  )

  assert.equal(result, current)
  assert.notEqual(result.items, inherited)
  assert.deepEqual([...result.items], [['new', { value: 2 }]])
  assert.deepEqual([...inherited], [['old', { value: 1 }]])
})

it('still reuses an existing own child', () => {
  const inherited = { value: 1 }
  const own = { value: 2 }
  const current = Object.assign(Object.create({ item: inherited }) as { item: typeof own }, {
    item: own,
  })
  const result = reconcile(current, { item: { value: 3 } })

  assert.equal(result, current)
  assert.equal(result.item, own)
  assert.equal(own.value, 3)
  assert.equal(inherited.value, 1)
})
