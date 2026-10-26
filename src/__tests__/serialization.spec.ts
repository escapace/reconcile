import { describe, expect, expectTypeOf, it } from 'vitest'
import { deserialize, type DeserializeOptions, isReconcileError, serialize } from '../index'
import { decodeText, encodeText } from './fixtures/text-codec'

const copy = <T>(value: T): T => decodeText(encodeText(value)) as T

describe('serialization', () => {
  it('exposes synchronous unknown boundaries and ordinary JSON text', () => {
    expectTypeOf(serialize).toEqualTypeOf<(value: unknown) => unknown>()
    expectTypeOf(deserialize).toEqualTypeOf<
      (json: unknown, options: DeserializeOptions) => unknown
    >()
    // The control table: the root's layout id 0, one shape of two keys, the layout [0, 0].
    expect(JSON.parse(encodeText({ count: 3, title: 'hello' }))).toEqual([
      [0, 1, 2, 'count', 'title', 2, 0, 0],
      [[3, 'hello']],
    ])
    expect(encodeText([-1, 'x', null])).toBe('[[0,0,1,2],[[-1,"x",null]]]')
    expect(encodeText(-1.5)).toBe('[-1.5]')
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

  it('decodes the JSON data it is handed and checks maxBytes first', () => {
    const shared = { label: 'shared' }
    const copied = deserialize(serialize({ a: shared, b: shared }), { maxBytes: Infinity }) as {
      a: object
      b: object
    }
    expect(copied.a).toBe(copied.b)
    expect(copied.a).not.toBe(shared)
    const limitCause = (options: unknown) => {
      try {
        deserialize(serialize(1), options as DeserializeOptions)
      } catch (error) {
        return isReconcileError(error) ? error.cause : error
      }
      return undefined
    }
    for (const maxBytes of [undefined, -1, 1.5, NaN, -Infinity, '10', 2 ** 53, null])
      expect(limitCause({ maxBytes })).toEqual({ maxBytes, type: 'DeserializeLimitInvalid' })
    expect(limitCause(undefined)).toEqual({ maxBytes: undefined, type: 'DeserializeLimitInvalid' })
    // Text is not JSON data: deserialize does not parse it.
    expect(() => deserialize('[1]', { maxBytes: Infinity })).toThrow(/envelope/)
  })

  it('rejects invalid runs, references, node order and natives', () => {
    for (const text of [
      '[[0,0,2,2,1],[[1]]]',
      '[[0,0,3,2,1,0],[[1,0,1]]]',
      '[[0,0,2,2,0],[[0.5]]]',
      '[[0,0,2,2,0],[[1]]]',
      '[[0,1,0,1,2,1,2],[[],[]]]',
      '[[1,0,0,1,2,1,6],[[null],[]]]',
      '[[0,0,1,18],[["-0"]]]',
      '[[0,0,1,6],[[-0]]]',
      '[[0,1,2,1,"a",1,"a",2,0,0,2,0,1],[[1],[2]]]',
      '[[0,0,1,3],[[2,[],[1,2]]]]',
      '[[0,0,1,3],[[2,[2],[1,2]]]]',
      '[[0,0,1,3],[[0,[0],[]]]]',
      '[[0,1,1,0,1,9,1,11],[["https://a.example/"],[0],[0]]]',
      '[[0,0,1,9],[["https://a.example/"]]]',
      '[[0,1,0,2,8,1,1,6],[[1,0,0],[0]]]',
      '[[0,1,1,0,2,2,0,1,2],[[2,1],[],[]]]',
      '[[0,1,0,2,2,0,1,2],[[0],[]]]',
    ])
      expect(() => decodeText(text)).toThrow(
        expect.objectContaining({
          cause: { reason: expect.any(String) as unknown, type: 'DeserializeInputInvalid' },
        }),
      )
  })

  it('accepts tables in any order, with repeats or unused entries, as given', () => {
    const cases: Array<[string, unknown]> = [
      ['[[0,1,2,0,2,2,0,1,13,1,18],[[1,1,2],[],["-0x5"]]]', [undefined, undefined, -5n]],
      ['[[0,0,1,2,1,6],[[]]]', []],
      ['[[0,1,0,1,2],[[]]]', []],
      ['[[0,1,2,0,2,2,0,1,13,1,13],[[1,2],[],[]]]', [undefined, undefined]],
      ['[[0,1,1,0,2,2,0,1,18],[[1,2],["0x5"],["0x5"]]]', [5n, 5n]],
      ['[[0,1,2,0,2,2,0,1,2,1,2],[[1,2],[],[]]]', [[], []]],
    ]
    for (const [text, value] of cases) expect(decodeText(text)).toEqual(value)
  })

  it('takes any JSON value in a literal slot as JSON.parse produced it', () => {
    const cases: Array<[string, unknown]> = [
      ['[-0]', -0],
      ['[1e400]', Infinity],
      ['[[1,{"a":null}]]', [1, { a: null }]],
      ['[{}]', {}],
      ['[[0,0,1,2],[[-0,-1e400]]]', [-0, -Infinity]],
      ['[[0,0,1,2],[[[1],{}]]]', [[1], {}]],
      [
        '[[0,1,1,"x",2,0,0],[[{"__proto__":[1]}]]]',
        { x: JSON.parse('{"__proto__":[1]}') as unknown },
      ],
    ]
    for (const [text, value] of cases) expect(decodeText(text)).toEqual(value)
    // A composite literal is a fresh value, never shared with another slot.
    const [first, second] = decodeText('[[0,0,1,2],[[[1],[1]]]]') as unknown[][]
    expect(first).not.toBe(second)
    const record = decodeText('[[0,1,1,"x",2,0,0],[[{"__proto__":[1]}]]]') as { x: object }
    expect(Object.getPrototypeOf(record.x)).toBe(Object.prototype)
    expect(Object.getOwnPropertyNames(record.x)).toEqual(['__proto__'])
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
    expect(encodeText(nested)).toBe(
      '[[0,1,2,2,2,"a","c",1,"b",4,0,0,0,1,2,3,1,2,0,1],[[1,3],[3,[1,1],[1,2]],[2]]]',
    )
    expect(log).toEqual([
      'proto root',
      // Names, then the enumerable keys that tell whether any name is hidden.
      'ownKeys root',
      'ownKeys root',
      'get root.a',
      'proto list',
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
      'ownKeys inner',
      'get inner.b',
      'ownKeys inner',
      'get list.length',
      'get root.c',
      'ownKeys root',
    ])

    // A Map is walked by the built-in iterator, never an own `entries`; a key's exception stops
    // the walk.
    log.length = 0
    const failure = new Error('key')
    const map = new Map<unknown, unknown>([
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
    ])
    map.entries = () => {
      log.push('entries')
      return new Map().entries()
    }
    expect(() => encodeText(map)).toThrow(failure)
    expect(log).toEqual(['key getter', 'value getter', 'throwing key'])

    log.length = 0
    const list: unknown[] = [1]
    list.push({
      get grow() {
        log.push('grow')
        list.push('tail')
        return 2
      },
    })
    expect(encodeText(spy(list, 'list'))).toBe(
      '[[0,1,1,1,"grow",3,2,1,1,2,0,0],[[1,1,"tail"],[2]]]',
    )
    expect(log).toEqual([
      'proto list',
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
      expect(() => encodeText(value)).toThrow(
        expect.objectContaining({
          cause: { reason: expect.any(String) as unknown, type: 'SerializeValueUnsupported' },
        }),
      )
    }
    for (const text of ['{}', '[[0],[]]', '[[0,0,1,100],[[]]]', '[[0,0,1,7],[["!"]]]']) {
      expect(() => decodeText(text)).toThrow(
        expect.objectContaining({
          cause: { reason: expect.any(String) as unknown, type: 'DeserializeInputInvalid' },
        }),
      )
    }
    expect(() => decodeText('{')).toThrow(SyntaxError)
    const failure = new Error('application')
    expect(() =>
      encodeText({
        get value() {
          throw failure
        },
      }),
    ).toThrow(failure)
  })
})
