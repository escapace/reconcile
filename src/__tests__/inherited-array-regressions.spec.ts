import { assert, it } from 'vitest'

import { produce, reconcile, ReconcileError } from '../index'

const inheritedArray = <T>(value: T): T[] => {
  const prototype = Object.create(Array.prototype) as T[]
  prototype[0] = value
  const array = new Array<T>(1)
  Object.setPrototypeOf(array, prototype)
  return array
}

it('creates an own array element without mutating an inherited object', () => {
  const inherited = { value: 1 }
  const current = inheritedArray(inherited)
  const result = reconcile(current, [{ value: 2 }])

  assert.equal(result, current)
  assert.isTrue(Object.hasOwn(result, 0))
  assert.notEqual(result[0], inherited)
  assert.equal(result[0].value, 2)
  assert.equal(inherited.value, 1)
})

it.each([undefined, 0, 'same'])(
  'publishes an own element for an equal inherited value %s',
  (value) => {
    const current = inheritedArray(value)
    const result = reconcile(
      current,
      produce(current, () => [value]),
    )

    assert.equal(result, current)
    assert.isTrue(Object.hasOwn(result, 0))
    assert.equal(result[0], value)
  },
)

it.each([false, true])(
  'rejects an unrepresentable root hole over an inherited index with own element = %s',
  (hasOwn) => {
    const inherited = { value: 1 }
    const current = inheritedArray(inherited)
    if (hasOwn) current[0] = { value: 2 }
    assert.throws(() => reconcile(current, new Array<typeof inherited>(1)), ReconcileError)
    assert.equal(inherited.value, 1)
  },
)

it('defines an own index when a wrapper ignores assignment', () => {
  const current = new Proxy(inheritedArray(2), {
    set(target, key, value) {
      return key === '0' || Reflect.set(target, key, value)
    },
  })
  const result = reconcile(current, [2])

  assert.equal(result, current)
  assert.isTrue(Object.hasOwn(result, 0))
  assert.equal(result[0], 2)
})

it('continues to reuse an existing own array child', () => {
  const inherited = { value: 1 }
  const own = { value: 2 }
  const current = inheritedArray(inherited)
  current[0] = own
  const result = reconcile(current, [{ value: 3 }])

  assert.equal(result, current)
  assert.equal(result[0], own)
  assert.equal(own.value, 3)
  assert.equal(inherited.value, 1)
})
