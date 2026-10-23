import { describe, expect, it } from 'vitest'
import { serialize } from '../index'
import { decodeText, encodeText } from './fixtures/text-codec'

describe('serialization collection iteration', () => {
  it('keeps first insertion order and the last value after a native Map revisit', () => {
    const trace: string[] = []
    let moved = false
    const oldValue = {
      get value() {
        trace.push('old')
        return 1
      },
    }
    const newValue = {
      get value() {
        trace.push('new')
        return 2
      },
    }
    const key = {
      get value() {
        trace.push('key')
        if (!moved) {
          moved = true
          source.delete(key)
          source.set(key, newValue)
        }
        return 0
      },
    }
    const source = new Map<unknown, unknown>()
    source.set(key, oldValue)
    source.set('middle', 3)
    const result = decodeText(encodeText(source)) as Map<unknown, unknown>
    expect(trace).toEqual(['key', 'old', 'new'])
    expect([...result.keys()]).toEqual([{ value: 0 }, 'middle'])
    expect([...result.values()]).toEqual([{ value: 2 }, 3])
  })

  it('keeps the first occurrence after a native Set revisit', () => {
    const trace: string[] = []
    let moved = false
    const member = {
      get value() {
        trace.push('member')
        if (!moved) {
          moved = true
          source.delete(member)
          source.add(member)
        }
        return 1
      },
    }
    const source = new Set<unknown>([member, 'middle'])
    const result = decodeText(encodeText(source)) as Set<unknown>
    expect(trace).toEqual(['member'])
    expect([...result]).toEqual([{ value: 1 }, 'middle'])
  })

  // serialize reads a Map's entries and a Set's members with the built-ins, so an override of
  // `entries` or `values` is never called.
  it("encodes a Map's built-in entries, never an overridden entries method", () => {
    const source = new Map<unknown, unknown>([
      [NaN, 4],
      // eslint-disable-next-line perfectionist/sort-maps -- the order is the case
      [-0, 5],
      ['middle', 3],
    ])
    Object.defineProperty(source, 'entries', {
      *value() {
        yield ['junk', 0]
      },
    })
    const result = decodeText(encodeText(source)) as Map<unknown, unknown>
    expect([...result]).toEqual([
      [NaN, 4],
      [0, 5],
      ['middle', 3],
    ])
  })

  it("encodes a Set's built-in members, never an overridden values method", () => {
    // eslint-disable-next-line perfectionist/sort-sets -- the order is the case
    const source = new Set<unknown>([NaN, -0, 'middle'])
    Object.defineProperty(source, 'values', {
      *value() {
        yield 'junk'
      },
    })
    const result = decodeText(encodeText(source)) as Set<unknown>
    expect([...result]).toEqual([NaN, 0, 'middle'])
  })

  it('preserves aliases, cycles and distinct equal objects across entries', () => {
    const shared = { value: 1 }
    const equal = { value: 1 }
    const map = new Map<unknown, unknown>()
    map.set(shared, map).set(equal, map)
    const set = new Set<unknown>()
    set.add(shared).add(set).add(equal)
    const source = { equal, map, set, shared }
    const result = decodeText(encodeText(source)) as typeof source
    expect(result.shared).not.toBe(result.equal)
    expect([...result.map.keys()]).toEqual([result.shared, result.equal])
    expect(result.map.get(result.shared)).toBe(result.map)
    expect(result.map.get(result.equal)).toBe(result.map)
    expect([...result.set]).toEqual([result.shared, result.set, result.equal])
  })

  it("lets a value's exception through the built-in walk of a Map", () => {
    const trace: string[] = []
    const failure = new Error('value getter')
    const source = new Map<unknown, unknown>([
      ['first', 1],
      [
        'key',
        {
          get value() {
            trace.push('value')
            throw failure
          },
        },
      ],
    ])
    let thrown: unknown
    try {
      encodeText(source)
    } catch (error) {
      thrown = error
    }
    expect(thrown).toBe(failure)
    expect(trace).toEqual(['value'])
  })

  it('validates every repeated Map value and Set member before insertion', () => {
    for (const text of [
      '[[0,0,3,4,1,1],[["key",1,"key",1]]]',
      '[[0,0,2,4,3],[["key",1,"key",1]]]',
      '[[0,0,2,5,2],[["member","member",1]]]',
    ])
      expect(() => decodeText(text)).toThrow(
        expect.objectContaining({
          cause: { reason: 'reference', type: 'DeserializeInputInvalid' },
        }),
      )
  })

  it('folds equal bigint keys and rejects noncanonical bigint text', () => {
    const result = decodeText('[[0,1,0,5,4,0,1,1,1,1,18],[[1,1,1,2],["0x0"]]]') as Map<
      unknown,
      unknown
    >
    expect([...result]).toEqual([[0n, 2]])
    const repeated = decodeText('[[0,1,1,0,5,4,0,1,1,1,1,18],[[1,1,2,2],["0x0"],["0x0"]]]') as Map<
      unknown,
      unknown
    >
    expect([...repeated]).toEqual([[0n, 2]])
    for (const digits of [
      '0',
      '1',
      'ff',
      '0x01',
      '-0x0',
      '0xFF',
      '0X1',
      ' 0x1',
      '0x1 ',
      '0x',
      '-0x',
      '+0x1',
      '0xg',
      '0b1',
    ])
      expect(() =>
        decodeText(`[[0,1,0,3,4,1,1,1,18],[["key",1,"key",1],[${JSON.stringify(digits)}]]]`),
      ).toThrow(
        expect.objectContaining({ cause: { reason: 'bigint', type: 'DeserializeInputInvalid' } }),
      )
  })

  it('writes bigints as a sign, 0x and lowercase hexadecimal digits', () => {
    const values = [0n, 1n, -1n, 255n, -256n, 2n ** 64n, -(2n ** 200n) + 1n]
    for (const value of values) {
      const document = serialize(value) as [unknown[], unknown[][]]
      const digits = value < 0n ? `-0x${(-value).toString(16)}` : `0x${value.toString(16)}`
      expect(document[1]).toEqual([[digits]])
      expect(decodeText(JSON.stringify(document))).toBe(value)
    }
    // One value repeated is written once and decoded at every occurrence.
    const shared = 2n ** 100n
    expect(decodeText(encodeText([shared, shared, -shared]))).toEqual([shared, shared, -shared])
  })

  it('decodes a large bigint in linear time', () => {
    const digits = 'f'.repeat(1_000_000)
    const start = performance.now()
    const value = decodeText(JSON.stringify([[0, 0, 1, 18], [[`0x${digits}`]]])) as bigint
    const elapsed = performance.now() - start
    expect(value).toBe(BigInt(`0x${digits}`))
    // Decimal text of this size takes about 250 ms on Node 24; hexadecimal takes a few.
    expect(elapsed).toBeLessThan(100)
  })
})
