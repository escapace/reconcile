import { afterEach, describe, expect, it } from 'vitest'
import { deserialize, produce, reconcile, serialize, snapshot } from '../index'

// Every function reads and writes the contents of a Map, Set, Date, URL or URLSearchParams with
// the built-in methods read at import: an override that a subclass, the instance or a later change
// to a standard prototype provides is never called.

const calls: string[] = []
const record = (name: string) => calls.push(name)

class CountingMap extends Map<unknown, unknown> {
  override clear(): void {
    record('map.clear')
    super.clear()
  }
  override delete(key: unknown): boolean {
    record('map.delete')
    return super.delete(key)
  }
  override entries(): MapIterator<[unknown, unknown]> {
    record('map.entries')
    return super.entries()
  }
  override forEach(...parameters: Parameters<Map<unknown, unknown>['forEach']>): void {
    record('map.forEach')
    super.forEach(...parameters)
  }
  override get(key: unknown): unknown {
    record('map.get')
    return super.get(key)
  }
  override has(key: unknown): boolean {
    record('map.has')
    return super.has(key)
  }
  override keys(): MapIterator<unknown> {
    record('map.keys')
    return super.keys()
  }
  override set(key: unknown, value: unknown): this {
    record('map.set')
    return super.set(key, value)
  }
  override get size(): number {
    record('map.size')
    return super.size
  }
  override [Symbol.iterator](): MapIterator<[unknown, unknown]> {
    record('map.iterator')
    return super[Symbol.iterator]()
  }
  override values(): MapIterator<unknown> {
    record('map.values')
    return super.values()
  }
}

class CountingSet extends Set<unknown> {
  override add(value: unknown): this {
    record('set.add')
    return super.add(value)
  }
  override clear(): void {
    record('set.clear')
    super.clear()
  }
  override delete(value: unknown): boolean {
    record('set.delete')
    return super.delete(value)
  }
  override has(value: unknown): boolean {
    record('set.has')
    return super.has(value)
  }
  override get size(): number {
    record('set.size')
    return super.size
  }
  override [Symbol.iterator](): SetIterator<unknown> {
    record('set.iterator')
    return super[Symbol.iterator]()
  }
  override values(): SetIterator<unknown> {
    record('set.values')
    return super.values()
  }
}

class CountingDate extends Date {
  override getTime(): number {
    record('date.getTime')
    return super.getTime()
  }
  override setTime(time: number): number {
    record('date.setTime')
    return super.setTime(time)
  }
}

const counting = () => ({
  date: new CountingDate(5),
  map: new CountingMap([
    ['a', { n: 1 }],
    ['b', 2],
  ]),
  set: new CountingSet([1, { m: 1 }]),
})

afterEach(() => {
  calls.length = 0
})

describe('built-in contents', () => {
  it('are read and copied by snapshot without any override', () => {
    const source = counting()
    calls.length = 0
    const copy = snapshot(source) as ReturnType<typeof counting>
    expect(calls).toEqual([])
    expect(Map.prototype.get.call(copy.map, 'b')).toBe(2)
    expect(Set.prototype.has.call(copy.set, 1)).toBe(true)
    expect(Date.prototype.getTime.call(copy.date)).toBe(5)
  })

  it('are read, kept and written by reconcile without any override', () => {
    const current = counting()
    const kept = { ...current }
    calls.length = 0
    reconcile(current, {
      date: new Date(9),
      map: new Map<unknown, unknown>([
        ['b', 3],
        ['c', { n: 2 }],
      ]),
      set: new Set<unknown>([2]),
    })
    expect(calls).toEqual([])
    expect(current.map).toBe(kept.map)
    expect([...Map.prototype.entries.call(current.map)]).toEqual([
      ['b', 3],
      ['c', { n: 2 }],
    ])
    expect([...Set.prototype.values.call(current.set)]).toEqual([2])
    expect(Date.prototype.getTime.call(current.date)).toBe(9)
  })

  it('are read and written through a draft without any override', () => {
    const current = counting()
    calls.length = 0
    const result = produce(current, (draft) => {
      draft.map.set('c', 3)
      draft.map.delete('a')
      expect(draft.map.get('b')).toBe(2)
      expect(draft.map.has('c')).toBe(true)
      expect(draft.map.size).toBe(2)
      expect([...draft.map.keys()]).toEqual(['b', 'c'])
      draft.map.forEach(() => undefined)
      draft.set.add(3)
      draft.set.delete(1)
      expect(draft.set.has(3)).toBe(true)
      expect(draft.set.size).toBe(2)
      // The recipe's own call of a method on its copy runs that method, as any call does.
      Date.prototype.setTime.call(draft.date, 7)
      return draft
    })
    expect(calls).toEqual([])
    expect(result.map).toBeInstanceOf(CountingMap)
    expect([...Map.prototype.keys.call(result.map)]).toEqual(['b', 'c'])
    expect(Set.prototype.has.call(result.set, 3)).toBe(true)
    expect(Date.prototype.getTime.call(result.date)).toBe(7)
  })

  it('are encoded by serialize without an own entries or values', () => {
    const map = new Map<unknown, unknown>([['a', 1]])
    const set = new Set<unknown>([1])
    Object.defineProperty(map, 'entries', { value: () => record('own entries') })
    Object.defineProperty(set, 'values', { value: () => record('own values') })
    const result = deserialize(JSON.parse(JSON.stringify(serialize({ map, set }))), {
      maxBytes: 1e4,
    }) as { map: Map<unknown, unknown>; set: Set<unknown> }
    expect(calls).toEqual([])
    expect([...result.map]).toEqual([['a', 1]])
    expect([...result.set]).toEqual([1])
  })

  it('ignore a standard prototype changed after import, on the values given and returned', () => {
    // The library's private tables are Maps and Sets too, so the patches record every receiver and
    // the test then asks which of them it gave or got back.
    const current = { map: new Map<unknown, unknown>([['a', 1]]), set: new Set<unknown>([1]) }
    const next = { map: new Map<unknown, unknown>([['b', 2]]), set: new Set<unknown>([2]) }
    const receivers: unknown[] = []
    const patched: Array<[object, PropertyKey, PropertyDescriptor]> = []
    const patch = (owner: object, key: PropertyKey) => {
      const descriptor = Object.getOwnPropertyDescriptor(owner, key)!
      patched.push([owner, key, descriptor])
      Object.defineProperty(
        owner,
        key,
        descriptor.get === undefined
          ? {
              ...descriptor,
              value(this: unknown, ...parameters: unknown[]) {
                receivers.push(this)
                return (descriptor.value as (...values: unknown[]) => unknown).apply(
                  this,
                  parameters,
                )
              },
            }
          : {
              ...descriptor,
              get(this: unknown) {
                receivers.push(this)
                return descriptor.get!.call(this) as unknown
              },
            },
      )
    }
    const keys = ['set', 'get', 'has', 'delete', 'clear', 'entries', 'forEach', 'size']
    for (const key of [...keys, Symbol.iterator]) patch(Map.prototype, key)
    for (const key of [
      'add',
      'has',
      'delete',
      'clear',
      'values',
      'forEach',
      'size',
      Symbol.iterator,
    ])
      patch(Set.prototype, key)
    let results: Array<typeof current> | undefined
    try {
      reconcile(current, next)
      const result = produce(current, (draft) => {
        draft.map.set('c', 3)
        draft.set.add(3)
        return draft
      })
      results = [
        current,
        next,
        result,
        snapshot(current) as typeof current,
        deserialize(serialize(current), { maxBytes: 1e4 }) as typeof current,
      ]
    } finally {
      for (const [owner, key, descriptor] of patched) Object.defineProperty(owner, key, descriptor)
    }
    const values = results.flatMap((value) => [value.map, value.set])
    expect(receivers.filter((receiver) => values.includes(receiver as never))).toEqual([])
    expect([...current.map]).toEqual([['b', 2]])
    expect([...results[3].set]).toEqual([2])
    expect([...results[2].map]).toEqual([
      ['b', 2],
      ['c', 3],
    ])
    expect([...results[2].set]).toEqual([2, 3])
    expect([...results[4].map]).toEqual([['b', 2]])
  })
})

const binaryValues = () => {
  const buffer = new ArrayBuffer(8)
  return {
    buffer,
    bytes: new Uint8Array(buffer, 0, 4),
    date: new Date(1),
    parameters: new URLSearchParams('a=1&b=2'),
    url: new URL('https://a.test/p?x=1'),
    view: new DataView(buffer, 2),
  }
}

// Defines on `target` a recording getter or method for each key, which calls the inherited one.
const shadow = (target: object, keys: readonly PropertyKey[]): void => {
  for (const key of keys) {
    let owner = Object.getPrototypeOf(target) as object | null
    let descriptor: PropertyDescriptor | undefined
    while (
      owner !== null &&
      (descriptor = Object.getOwnPropertyDescriptor(owner, key)) === undefined
    )
      owner = Object.getPrototypeOf(owner) as object | null
    const name = `override ${String(key)}`
    Object.defineProperty(
      target,
      key,
      descriptor!.get === undefined
        ? {
            configurable: true,
            value(this: unknown, ...parameters: unknown[]) {
              record(name)
              return (descriptor!.value as (...values: unknown[]) => unknown).apply(
                this,
                parameters,
              )
            },
          }
        : {
            configurable: true,
            get(this: unknown) {
              record(name)
              return descriptor!.get!.call(this) as unknown
            },
          },
    )
  }
}

const viewKeys = ['buffer', 'byteLength', 'byteOffset']
const overrides: Array<[new (...parameters: never[]) => object, readonly PropertyKey[]]> = [
  [ArrayBuffer, ['byteLength', 'slice']],
  [Uint8Array, [...viewKeys, 'length', 'set', 'subarray', 'slice']],
  [DataView, [...viewKeys, 'getUint8', 'setUint8']],
  [Date, ['getTime', 'setTime', 'valueOf']],
  [URL, ['href', 'search', 'searchParams', 'toString']],
  [URLSearchParams, ['append', 'delete', 'entries', 'keys', 'toString', Symbol.iterator]],
]

describe('built-in contents of dates, buffers, views and URLs', () => {
  it('run no override that a subclass or the instance defines, in every function', () => {
    const subclassed = () => {
      const values = binaryValues()
      const made: Record<string, object> = {}
      for (const [key, value] of Object.entries(values)) {
        const Base = overrides.find(([Kind]) => value instanceof Kind)!
        const Sub = class extends (Base[0] as new (...parameters: unknown[]) => object) {}
        shadow(Sub.prototype, Base[1])
        made[key] = Object.setPrototypeOf(value, Sub.prototype) as object
      }
      return made as typeof values
    }
    const current = subclassed()
    reconcile(current, subclassed())
    reconcile(current, { ...binaryValues(), date: new Date(9) })
    snapshot(current)
    produce(subclassed(), (draft) => {
      void draft.bytes
      void draft.view
      void draft.url
      void draft.parameters
      void draft.date
      return draft
    })
    const own = binaryValues()
    for (const value of Object.values(own))
      shadow(value, overrides.find(([Kind]) => value instanceof Kind)![1])
    deserialize(serialize(own), { maxBytes: 1e4 })
    expect(calls).toEqual([])
  })

  it('ignore every standard prototype changed after import, in every function', () => {
    const typed = Object.getPrototypeOf(Uint8Array.prototype) as object
    const patched: Array<[object, PropertyKey, PropertyDescriptor]> = []
    const patch = (owner: object, key: PropertyKey) => {
      const descriptor = Object.getOwnPropertyDescriptor(owner, key)!
      patched.push([owner, key, descriptor])
      const name = `patched ${String(key)}`
      Object.defineProperty(
        owner,
        key,
        descriptor.get === undefined
          ? {
              ...descriptor,
              value(this: unknown, ...parameters: unknown[]) {
                record(name)
                return (descriptor.value as (...values: unknown[]) => unknown).apply(
                  this,
                  parameters,
                )
              },
            }
          : {
              ...descriptor,
              get(this: unknown) {
                record(name)
                return descriptor.get!.call(this) as unknown
              },
            },
      )
    }
    for (const key of ['set', 'subarray', 'slice', 'length', 'buffer', 'byteLength', 'byteOffset'])
      patch(typed, key)
    for (const key of ['slice', 'byteLength']) patch(ArrayBuffer.prototype, key)
    for (const key of ['buffer', 'byteLength', 'byteOffset', 'getUint8', 'setUint8'])
      patch(DataView.prototype, key)
    for (const key of ['getTime', 'setTime', 'valueOf']) patch(Date.prototype, key)
    for (const key of ['href', 'search', 'searchParams', 'toString']) patch(URL.prototype, key)
    for (const key of ['append', 'delete', 'entries', 'keys', 'toString', Symbol.iterator])
      patch(URLSearchParams.prototype, key)
    let text: string | undefined
    try {
      const current = binaryValues()
      const next = binaryValues()
      Uint8Array.prototype.fill.call(next.bytes, 7)
      reconcile(current, {
        ...next,
        date: new Date(9),
        parameters: new URLSearchParams('c=3'),
        url: new URL('https://b.test/?y=2'),
      })
      snapshot(current)
      produce(current, (draft) => {
        Uint8Array.prototype.fill.call(draft.bytes, 1)
        void draft.view
        void draft.url
        void draft.parameters
        void draft.date
        return draft
      })
      text = JSON.stringify(serialize(current))
      deserialize(JSON.parse(text), { maxBytes: 1e4 })
    } finally {
      for (const [owner, key, descriptor] of patched) Object.defineProperty(owner, key, descriptor)
    }
    expect(calls).toEqual([])
    expect(text).toContain('b.test')
  })
})
