import { assert, it } from 'vitest'

import { deserialize, produce, reconcile, serialize, snapshot } from '../index'

// A proxy over an extensible target may list keys it reports no descriptor for. Every function
// treats such a key as absent, as Object.keys, object spread and JSON.stringify do.

const listedSymbol = Symbol('listed')

/** `target` behind a proxy that also lists `ghost` and a symbol, with no descriptor for either. */
const listing = <T extends object>(target: T): T =>
  new Proxy(target, { ownKeys: (t) => [...Reflect.ownKeys(t), 'ghost', listedSymbol] })

it('lists keys without descriptors as the platform does', () => {
  const value = listing({ a: 1 })
  assert.deepEqual(Object.keys(value), ['a'])
  assert.deepEqual(Reflect.ownKeys(value), ['a', 'ghost', listedSymbol])
  assert.equal(JSON.stringify(value), '{"a":1}')
})

it('snapshot leaves the keys out of the copy', () => {
  const copy = (snapshot({ value: listing({ a: 1 }) }) as { value: object }).value
  assert.deepEqual(Reflect.ownKeys(copy), ['a'])
})

it('serialize leaves the keys out instead of rejecting them', () => {
  const copy = deserialize(JSON.parse(JSON.stringify(serialize(listing({ a: 1 })))), {
    maxBytes: Infinity,
  })
  assert.deepEqual(copy, { a: 1 })
})

it('reconcile reads next without the keys', () => {
  const current: Record<PropertyKey, unknown> = { a: 0 }
  const result = reconcile(current, listing({ a: 1 }))
  assert.equal(result, current)
  assert.deepEqual(Reflect.ownKeys(current), ['a'])
  assert.equal(current.a, 1)
})

it('produce keeps an unchanged proxy and copies a changed one without the keys', () => {
  const held = listing({ a: 1 })
  // An unchanged subtree is kept, read or not, as any is.
  assert.ok(produce({ held }, (draft) => draft).held === held)
  const read = produce({ held }, (draft) => {
    assert.equal(draft.held.a, 1)
    return draft
  })
  assert.ok(read.held === held)
  const changed = produce({ held }, (draft) => {
    draft.held.a = 2
    return draft
  })
  assert.deepEqual(Reflect.ownKeys(changed.held), ['a'])
  assert.equal(changed.held.a, 2)
})
