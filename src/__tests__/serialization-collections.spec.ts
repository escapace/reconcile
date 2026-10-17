import { describe, expect, it } from 'vitest'
import { parse, stringify } from '../index'

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
    const result = parse(stringify(source)) as Map<unknown, unknown>
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
    const result = parse(stringify(source)) as Set<unknown>
    expect(trace).toEqual(['member'])
    expect([...result]).toEqual([{ value: 1 }, 'middle'])
  })

  it('uses SameValueZero for repeated keys from an overridden iterator', () => {
    const source = new Map<unknown, unknown>()
    Object.defineProperty(source, 'entries', {
      *value() {
        yield [NaN, 1]
        yield [-0, 2]
        yield ['middle', 3]
        yield [NaN, 4]
        yield [0, 5]
      },
    })
    const result = parse(stringify(source)) as Map<unknown, unknown>
    expect([...result]).toEqual([
      [NaN, 4],
      [0, 5],
      ['middle', 3],
    ])
  })

  it('uses SameValueZero for repeated members from an overridden iterator', () => {
    const source = new Set<unknown>()
    Object.defineProperty(source, 'values', {
      *value() {
        yield NaN
        yield -0
        yield 'middle'
        yield NaN
        yield 0
      },
    })
    const result = parse(stringify(source)) as Set<unknown>
    expect([...result]).toEqual([NaN, 0, 'middle'])
  })

  it('preserves aliases, cycles and distinct equal objects across repeated entries', () => {
    const shared = { value: 1 }
    const equal = { value: 1 }
    const map = new Map<unknown, unknown>()
    Object.defineProperty(map, 'entries', {
      *value() {
        yield [shared, shared]
        yield [equal, map]
        yield [shared, map]
      },
    })
    const set = new Set<unknown>()
    Object.defineProperty(set, 'values', {
      *value() {
        yield shared
        yield set
        yield equal
        yield shared
      },
    })
    const source = { equal, map, set, shared }
    const result = parse(stringify(source)) as typeof source
    expect(result.shared).not.toBe(result.equal)
    expect([...result.map.keys()]).toEqual([result.shared, result.equal])
    expect(result.map.get(result.shared)).toBe(result.map)
    expect(result.map.get(result.equal)).toBe(result.map)
    expect([...result.set]).toEqual([result.shared, result.set, result.equal])
  })

  it('traverses repeated values and preserves abrupt completion cleanup', () => {
    const trace: string[] = []
    const failure = new Error('repeated value getter')
    const source = new Map<unknown, unknown>()
    Object.defineProperty(source, 'entries', {
      *value() {
        try {
          yield ['key', 1]
          yield [
            'key',
            {
              get value() {
                trace.push('repeated')
                throw failure
              },
            },
          ]
          trace.push('unreachable')
        } finally {
          trace.push('close')
        }
      },
    })
    let thrown: unknown
    try {
      stringify(source)
    } catch (error) {
      thrown = error
    }
    expect(thrown).toBe(failure)
    expect(trace).toEqual(['repeated', 'close'])
  })

  it('validates every repeated Map value and Set member before insertion', () => {
    for (const text of [
      '[[],[[4,1,1]],[0],[["key",1,"key",1]]]',
      '[[],[[4,3]],[0],[["key",1,"key",1]]]',
      '[[],[[5,2]],[0],[["member","member",1]]]',
    ])
      expect(() => parse(text)).toThrow(
        expect.objectContaining({ cause: { reason: 'reference', type: 'ParseInputInvalid' } }),
      )
  })

  it('shares bigint keys and rejects noncanonical or repeated bigint nodes', () => {
    const result = parse('[[],[[4,0,1,1,1],[18]],[0,1],[[1,1,1,2],["0"]]]') as Map<unknown, unknown>
    expect([...result]).toEqual([[0n, 2]])
    for (const text of [
      '[[],[[4,1,1],[18]],[0,1],[["key",1,"key",1],["01"]]]',
      '[[],[[4,1,1],[18]],[0,1],[["key",1,"key",1],["-0"]]]',
      '[[],[[4,0,1,1,1],[18]],[0,1,1],[[1,1,2,2],["0"],["0"]]]',
    ])
      expect(() => parse(text)).toThrow(
        expect.objectContaining({ cause: { reason: 'bigint', type: 'ParseInputInvalid' } }),
      )
  })
})
