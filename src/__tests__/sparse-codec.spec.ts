import { assert, it } from 'vitest'
import { parse } from '../index'

it.each([0, 1, 4_294_967_295])('decodes an all-hole sparse shell of length %s', (length) => {
  // Length zero has no hole and is the dense empty array.
  const payload = length === 0 ? [] : [length, [0], []]
  const result = parse(JSON.stringify([[], [[length === 0 ? 2 : 3]], [0], [payload]])) as unknown[]
  assert.isTrue(Array.isArray(result))
  assert.equal(Object.getPrototypeOf(result), Array.prototype)
  assert.isTrue(Object.isExtensible(result))
  assert.deepEqual(Reflect.ownKeys(result), ['length'])
  assert.deepEqual(Object.getOwnPropertyDescriptor(result, 'length'), {
    configurable: false,
    enumerable: false,
    value: length,
    writable: true,
  })
})

it('fills sparse maximum-index cycles and preserves aliases and default descriptors', () => {
  const result = parse(
    JSON.stringify([
      [],
      [
        [2, 0],
        [3, 0],
      ],
      [0, 1],
      [
        [1, 1],
        [4_294_967_295, [1, 4_294_967_293], [1, 0]],
      ],
    ]),
  ) as unknown[][]
  const sparse = result[0]
  assert.equal(sparse, result[1])
  assert.equal(sparse[0], sparse)
  assert.equal(sparse[4_294_967_294], result)
  assert.equal(sparse.length, 4_294_967_295)
  assert.deepEqual(Reflect.ownKeys(sparse), ['0', '4294967294', 'length'])
  for (const index of [0, 4_294_967_294])
    assert.deepEqual(Object.getOwnPropertyDescriptor(sparse, index), {
      configurable: true,
      enumerable: true,
      value: sparse[index],
      writable: true,
    })
})

it('keeps sparse decoder allocation separate from own prototype data', () => {
  const before = Object.getOwnPropertyDescriptors(Object.prototype)
  const result = parse(
    JSON.stringify([
      [['__proto__']],
      [
        [0, 0, 0],
        [3, 0],
      ],
      [0, 1],
      [[1], [3, [0, 1, 1], [0]]],
    ]),
  ) as Record<string, unknown>
  assert.equal(Object.getPrototypeOf(result), Object.prototype)
  const sparse = Object.getOwnPropertyDescriptor(result, '__proto__')!.value as unknown[]
  assert.equal(Object.getPrototypeOf(sparse), Array.prototype)
  assert.equal(sparse[1], result)
  assert.deepEqual(Object.keys(sparse), ['1'])
  assert.deepEqual(Object.getOwnPropertyDescriptors(Object.prototype), before)
})
