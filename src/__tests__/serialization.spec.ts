import { describe, expect, expectTypeOf, it } from 'vitest'
import { parse, stringify } from '../index'

const copy = <T>(value: T): T => parse(stringify(value)) as T

describe('serialization', () => {
  it('exposes synchronous unknown boundaries and ordinary JSON text', () => {
    expectTypeOf(stringify).toEqualTypeOf<(value: unknown) => string>()
    expectTypeOf(parse).toEqualTypeOf<(text: string) => unknown>()
    expect(JSON.parse(stringify({ count: 3, title: 'hello' }))).toEqual([
      -6,
      [['count', 'title']],
      [[0, 0, 3, 'hello']],
    ])
    for (const value of [
      undefined,
      null,
      true,
      'text',
      0,
      -0,
      -1.25,
      NaN,
      Infinity,
      -Infinity,
      123n,
      -123n,
    ])
      expect(Object.is(copy(value), value)).toBe(true)
  })

  it('rejects legacy singleton special tokens', () => {
    for (const tag of [-1, -2, -3, -4, -5])
      expect(() => parse(JSON.stringify([[tag], [], []]))).toThrow()
  })

  it('preserves cycles, shared identities and distinct equal objects in collections', () => {
    const child = { value: 1 }
    const source = {
      child,
      equal: { value: 1 },
      map: new Map<unknown, unknown>(),
      second: child,
      set: new Set<unknown>(),
    }
    source.map.set(source, child)
    source.set.add(source)
    const result = copy(source)
    expect(result).not.toBe(source)
    expect(result.child).toBe(result.second)
    expect(result.child).not.toBe(result.equal)
    expect(result.map.get(result)).toBe(result.child)
    expect(result.set.has(result)).toBe(true)
  })

  it('preserves sparse slots and captures record values once in depth-first order', () => {
    const trace: string[] = []
    const source = {
      get first() {
        trace.push('first')
        return {
          get nested() {
            trace.push('nested')
            return 1
          },
        }
      },
      get last() {
        trace.push('last')
        return 2
      },
    }
    expect(copy(source)).toEqual({ first: { nested: 1 }, last: 2 })
    expect(trace).toEqual(['first', 'nested', 'last'])
    const sparse = new Array<unknown>(4)
    sparse[2] = undefined
    const result = copy(sparse)
    expect(result.length).toBe(4)
    expect(0 in result).toBe(false)
    expect(2 in result).toBe(true)
  })

  it('observes proxies, holes, Map entries and growing arrays in source order', () => {
    const log: string[] = []
    const spy = <T extends object>(target: T, label: string): T =>
      new Proxy(target, {
        get(object, key, receiver) {
          log.push(`get ${label}.${String(key)}`)
          return Reflect.get(object, key, receiver) as unknown
        },
        getPrototypeOf(object) {
          log.push(`proto ${label}`)
          return Reflect.getPrototypeOf(object)
        },
        has(object, key) {
          log.push(`has ${label}.${String(key)}`)
          return Reflect.has(object, key)
        },
        ownKeys(object) {
          log.push(`ownKeys ${label}`)
          return Reflect.ownKeys(object)
        },
      })
    // eslint-disable-next-line no-sparse-arrays -- The hole is the observed case.
    const nested = spy({ a: spy([1, , spy({ b: 2 }, 'inner')], 'list'), c: 3 }, 'root')
    expect(stringify(nested)).toBe('[-6,[["a","c"],["b"]],[[0,0,-7,3],[3,3,0,1,2,-8],[0,1,2]]]')
    expect(log).toEqual([
      'proto root',
      'ownKeys root',
      'get root.a',
      'proto list',
      'get list.length',
      'get list.length',
      'has list.0',
      'get list.0',
      'get list.length',
      'has list.1',
      'get list.length',
      'has list.2',
      'get list.2',
      'proto inner',
      'ownKeys inner',
      'get inner.b',
      'ownKeys inner',
      'get list.length',
      'get root.c',
      'ownKeys root',
    ])

    log.length = 0
    const failure = new Error('key')
    const map = new Map()
    let step = 0
    const entries = [
      [
        {
          get k() {
            log.push('key getter')
            return 1
          },
        },
        {
          get v() {
            log.push('value getter')
            return 2
          },
        },
      ],
      [
        {
          get k() {
            log.push('throwing key')
            throw failure
          },
        },
        3,
      ],
    ]
    map.entries = () =>
      ({
        next() {
          log.push('next')
          return step < entries.length ? { done: false, value: entries[step++] } : { done: true }
        },
        return() {
          log.push('return')
          return {}
        },
        [Symbol.iterator]() {
          return this
        },
      }) as unknown as MapIterator<[unknown, unknown]>
    expect(() => stringify(map)).toThrow(failure)
    expect(log).toEqual(['next', 'key getter', 'value getter', 'next', 'throwing key', 'return'])

    log.length = 0
    const list: unknown[] = [1]
    list.push({
      get grow() {
        log.push('grow')
        list.push('tail')
        return 2
      },
    })
    expect(stringify(spy(list, 'list'))).toBe('[-6,[["grow"]],[[2,3,1,-7,"tail"],[0,0,2]]]')
    expect(log).toEqual([
      'proto list',
      'get list.length',
      'get list.length',
      'has list.0',
      'get list.0',
      'get list.length',
      'has list.1',
      'get list.1',
      'grow',
      'get list.length',
      'has list.2',
      'get list.2',
      'get list.length',
    ])
  })

  it('defines dangerous record keys as data without polluting prototypes', () => {
    const source = Object.create(null) as Record<string, unknown>
    Object.defineProperty(source, '__proto__', { enumerable: true, value: { polluted: true } })
    Object.defineProperty(source, 'constructor', { enumerable: true, value: 'value' })
    const result = copy(source)
    expect(Object.getPrototypeOf(result)).toBeNull()
    expect(Object.getOwnPropertyDescriptor(result, '__proto__')?.value).toEqual({ polluted: true })
    expect(Object.hasOwn(Object.prototype, 'polluted')).toBe(false)
    const ordinary = JSON.parse('{"__proto__":{"polluted":true}}') as object
    expect(Object.getPrototypeOf(copy(ordinary))).toBe(Object.prototype)
  })

  it('preserves fixed backing-store aliases, view spans and native state despite shadows', () => {
    const storage = new ArrayBuffer(16)
    const bytes = new Uint8Array(storage, 2, 4)
    bytes.set([1, 2, 3, 4])
    const view = new DataView(storage, 4, 8)
    Object.defineProperty(bytes, 'buffer', {
      get() {
        throw new Error('shadow')
      },
    })
    const result = copy({ bytes, storage, view })
    expect(result.storage).not.toBe(storage)
    expect(result.bytes.buffer).toBe(result.storage)
    expect(result.view.buffer).toBe(result.storage)
    expect(result.bytes.byteOffset).toBe(2)
    expect(result.view.byteLength).toBe(8)
    expect([...result.bytes]).toEqual([1, 2, 3, 4])
    const date = new Date(123)
    date.getTime = () => {
      throw new Error('shadow')
    }
    expect(copy(date).getTime()).toBe(123)
    expect(Number.isNaN(copy(new Date(NaN)).getTime())).toBe(true)
  })

  it('preserves URL ownership and raw query in either discovery order', () => {
    for (const first of ['parameters', 'owner']) {
      const owner = new URL('https://example.com/?a=b%20c')
      const source =
        first === 'parameters'
          ? { ...{ parameters: owner.searchParams }, owner }
          : { owner, parameters: owner.searchParams }
      expect(Object.keys(source)[0]).toBe(first)
      const result = copy(source)
      expect(result.owner.href).toBe(owner.href)
      expect(result.parameters).toBe(result.owner.searchParams)
      result.parameters.append('next', 'value')
      expect(result.owner.search).toContain('next=value')
      expect(owner.search).not.toContain('next=value')
    }
  })

  it('classifies unsupported values and malformed structures while preserving native errors', () => {
    for (const value of [Symbol('x'), () => 1, /x/, new Number(1), new WeakMap()]) {
      expect(() => stringify(value)).toThrow(
        expect.objectContaining({
          cause: { reason: expect.any(String) as unknown, type: 'StringifyValueUnsupported' },
        }),
      )
    }
    for (const text of ['{}', '[-6,[],[]]', '[0,[],[[100]]]', '[0,[],[[7,"!"]]]']) {
      expect(() => parse(text)).toThrow(
        expect.objectContaining({
          cause: { reason: expect.any(String) as unknown, type: 'ParseInputInvalid' },
        }),
      )
    }
    expect(() => parse('{')).toThrow(SyntaxError)
    const failure = new Error('application')
    expect(() =>
      stringify({
        get value() {
          throw failure
        },
      }),
    ).toThrow(failure)
  })
})
