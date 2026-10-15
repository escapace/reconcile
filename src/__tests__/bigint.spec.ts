/* eslint-disable perfectionist/sort-maps, perfectionist/sort-sets -- Collection insertion order is part of these regression fixtures. */
import { assert, describe, it } from 'vitest'

import { produce } from '../produce'
import { reconcile } from '../reconcile'
import { snapshot } from '../snapshot'

describe('bigint values', () => {
  it('preserves arbitrary precision primitive roots in every operation', () => {
    const value = -(1n << 200n) + 17n
    assert.strictEqual(snapshot(value), value)
    assert.strictEqual(reconcile(0n, value), value)
    assert.strictEqual(
      produce(value, (draft) => draft + 1n),
      value + 1n,
    )
    assert.strictEqual(
      produce(value, (draft) => draft),
      value,
    )
  })

  it('preserves bigint values, collection order and graph identities', () => {
    const value = 1n << 100n
    const shared = { value }
    const source = {
      first: shared,
      map: new Map<bigint | number, unknown>([
        [value, shared],
        [1n, 'bigint'],
        [1, 'number'],
      ]),
      second: shared,
      set: new Set<bigint | number>([value, 1n, 1]),
    }
    source.map.set(-value, source)
    const result = snapshot(source) as typeof source
    assert.notStrictEqual(result, source)
    assert.notStrictEqual(result.first, shared)
    assert.strictEqual(result.first, result.second)
    assert.strictEqual(result.map.get(value), result.first)
    assert.strictEqual(result.map.get(-value), result)
    assert.deepEqual([...result.map.keys()], [value, 1n, 1, -value])
    assert.deepEqual([...result.set], [value, 1n, 1])
  })

  it('updates bigint properties without changing the recipe input', () => {
    const current = { count: 2n, nested: { value: -(1n << 100n) } }
    const next = produce(current, (draft) => {
      draft.count += 1n
      draft.nested.value -= 1n
      return draft
    })
    assert.strictEqual(current.count, 2n)
    assert.strictEqual(current.nested.value, -(1n << 100n))
    const nested = current.nested
    assert.strictEqual(reconcile(current, next), current)
    assert.strictEqual(current.nested, nested)
    assert.strictEqual(current.count, 3n)
    assert.strictEqual(current.nested.value, -(1n << 100n) - 1n)
  })

  it('keeps signed and unsigned bigint views attached to one copied buffer', () => {
    const buffer = new ArrayBuffer(24)
    const signed = new BigInt64Array(buffer, 8, 2)
    const unsigned = new BigUint64Array(buffer, 8, 2)
    signed.set([-1n, -(1n << 63n)])
    const source = { again: signed, buffer, signed, unsigned }
    const result = snapshot(source) as typeof source
    assert.notStrictEqual(result.buffer, buffer)
    assert.strictEqual(result.signed.buffer, result.buffer)
    assert.strictEqual(result.unsigned.buffer, result.buffer)
    assert.strictEqual(result.again, result.signed)
    assert.strictEqual(result.signed.byteOffset, 8)
    assert.deepEqual([...result.signed], [-1n, -(1n << 63n)])
    assert.deepEqual([...result.unsigned], [(1n << 64n) - 1n, 1n << 63n])
    result.signed[0] = 3n
    assert.strictEqual(signed[0], -1n)
    assert.strictEqual(result.unsigned[0], 3n)
  })
})
