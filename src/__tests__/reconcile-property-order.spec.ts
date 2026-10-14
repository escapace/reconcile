/* eslint-disable perfectionist/sort-objects -- Key insertion order is the tested contract. */
import { assert, it } from 'vitest'

import { reconcile } from '../index'

it('retains a non-extensible root when only a leading property is removed', () => {
  const current = Object.preventExtensions({ obsolete: 0, retained: { value: 0 } })
  const retained = current.retained
  assert.equal(reconcile(current, { retained: { value: 1 } }), current)
  assert.deepEqual(Reflect.ownKeys(current), ['retained'])
  assert.equal(current.retained, retained)
  assert.equal(retained.value, 1)
})

it('retains an aligned nested object when a fixed key precedes an inserted key', () => {
  const child = { a: 0, fixed: 0, c: 0 }
  Object.defineProperty(child, 'fixed', { configurable: false })
  const current = { child }
  assert.equal(reconcile(current, { child: { a: 1, fixed: 1, inserted: 1, c: 1 } }), current)
  assert.equal(current.child, child)
  assert.deepEqual(Reflect.ownKeys(child), ['a', 'fixed', 'inserted', 'c'])
})

it.each(['1', '4294967294'])(
  'keeps a fixed canonical index %s when adding an earlier index',
  (key) => {
    const current = Object.defineProperty({ anchor: 0 }, key, {
      configurable: false,
      enumerable: true,
      value: 0,
      writable: true,
    })
    const next = { 0: 1, anchor: 1, [key]: 1 }
    assert.equal(reconcile(current, next), current)
    assert.deepEqual(Reflect.ownKeys(current), Reflect.ownKeys(next))
    assert.equal(Reflect.get(current, key), 1)
  },
)

it.each(['4294967295', '4294967296', '01', '-0', '+1', '1.0', '1e0', '', '1\n', ' 1', '１'])(
  'reorders non-index name %j as an ordinary string',
  (key) => {
    const current = { [key]: 0, anchor: 0 }
    const next = { anchor: 1, [key]: 1 }
    assert.equal(reconcile(current, next), current)
    assert.deepEqual(Reflect.ownKeys(current), ['anchor', key])
    assert.equal(Reflect.get(current, key), 1)
  },
)

it('orders symbol keys independently of newly inserted string keys', () => {
  const first = Symbol('first')
  const second = Symbol('second')
  const current = { before: 0, [first]: 0, [second]: 0 }
  Object.defineProperty(current, first, { configurable: false })
  const next = { before: 1, inserted: 1, [first]: 1, [second]: 1 }
  assert.equal(reconcile(current, next), current)
  assert.deepEqual(Reflect.ownKeys(current), Reflect.ownKeys(next))
})
