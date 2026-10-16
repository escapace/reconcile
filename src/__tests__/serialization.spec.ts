import { describe, expect, expectTypeOf, it } from 'vitest'
import { parse, stringify } from '../index'

const copy = <T>(value: T): T => parse(stringify(value)) as T

describe('serialization', () => {
  it('exposes synchronous unknown boundaries and ordinary JSON text', () => {
    expectTypeOf(stringify).toEqualTypeOf<(value: unknown) => string>()
    expectTypeOf(parse).toEqualTypeOf<(text: string) => unknown>()
    expect(JSON.parse(stringify({ count: 3, title: 'hello' }))).toEqual([
      -1,
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
          ? { owner, parameters: owner.searchParams }
          : { owner, parameters: owner.searchParams }
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
    for (const text of ['{}', '[-1,[],[]]', '[0,[],[[100]]]', '[0,[],[[7,"!"]]]']) {
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
