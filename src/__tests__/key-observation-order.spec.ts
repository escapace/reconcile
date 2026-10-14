import { assert, it } from 'vitest'

import { produce, reconcile } from '../index'
it('finalizes interleaved proxy keys in domain order while preserving data descriptors', () => {
  const first = Symbol('first')
  const second = Symbol('second')
  const keys = [second, 'c', first, 'a', 'b']
  const target = Object.fromEntries(keys.map((key) => [key, 0]))
  Object.defineProperty(target, 'a', { enumerable: false })
  const current = new Proxy(target, { ownKeys: () => keys })
  const next = produce(current, (draft) => {
    draft.b = 1
    return draft
  })
  assert.deepEqual(Reflect.ownKeys(next), ['c', 'a', 'b', second, first])
  assert.isFalse(Object.getOwnPropertyDescriptor(next, 'a')!.enumerable)
  assert.equal(next.b, 1)
  assert.equal(current.b, 0)
})

it('still discovers requested symbols introduced by a string getter before publication', () => {
  const added = Symbol('added')
  let reads = 0
  const requested: Record<PropertyKey, unknown> = {
    get value() {
      reads += 1
      requested[added] = { count: 2 }
      return 1
    },
  }
  const current: Record<PropertyKey, unknown> = {}
  assert.equal(reconcile(current, requested), current)
  assert.equal(reads, 1)
  assert.deepEqual(Reflect.ownKeys(current), ['value', added])
  assert.deepEqual(current[added], { count: 2 })
})
