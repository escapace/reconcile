import { describe, expect, it } from 'vitest'
import { produce, reconcile, snapshot } from '../index'

// A copy is built with the built-in operations: its class's constructor never ran, so an override
// that relies on a field the constructor sets would fail on it, and a setter on its prototype
// would drop the element.
const calls: string[] = []

class IndexedMap<K, V> extends Map<K, V> {
  readonly index = new Set<K>()
  override entries(): MapIterator<[K, V]> {
    calls.push('entries')
    return super.entries()
  }
  override set(key: K, value: V): this {
    calls.push('set')
    this.index.add(key)
    return super.set(key, value)
  }
}

class IndexedSet<T> extends Set<T> {
  readonly index: T[] = []
  override add(value: T): this {
    calls.push('add')
    this.index.push(value)
    return super.add(value)
  }
  override values(): SetIterator<T> {
    calls.push('values')
    return super.values()
  }
}

class Guarded<T> extends Array<T> {}
Object.defineProperty(Guarded.prototype, '0', {
  configurable: true,
  get: () => 'inherited',
  set: () => {
    calls.push('index')
  },
})

const entries = (map: Map<unknown, unknown>): unknown[] => [
  ...(Map.prototype.entries.call(map) as MapIterator<unknown>),
]
const members = (set: Set<unknown>): unknown[] => [
  ...(Set.prototype.values.call(set) as SetIterator<unknown>),
]

function sources() {
  const map = new IndexedMap<string, { v: number }>()
  map.set('a', { v: 1 })
  const set = new IndexedSet<{ v: number }>()
  set.add({ v: 1 })
  const array = new Guarded<number>()
  Object.defineProperty(array, '0', {
    configurable: true,
    enumerable: true,
    value: 5,
    writable: true,
  })
  array.length = 2
  array[1] = 6
  calls.length = 0
  return { array, map, set }
}

describe('copies of subclass instances', () => {
  it('are built by snapshot without set, add or prototype setters', () => {
    const source = sources()
    const copy = snapshot(source) as typeof source
    // Contents are read with the built-ins, never through the source's own methods.
    expect(calls).toEqual([])
    expect(copy.map).toBeInstanceOf(IndexedMap)
    expect(entries(copy.map)).toEqual([['a', { v: 1 }]])
    expect(members(copy.set)).toEqual([{ v: 1 }])
    expect(Object.hasOwn(copy.array, 0)).toBe(true)
    expect(copy.array[0]).toBe(5)
  })

  it('are built by produce without set, add or prototype setters', () => {
    const source = sources()
    const result = produce(source, (draft) => {
      draft.map.get('a')!.v = 2
      for (const member of draft.set) member.v = 2
      draft.array[1] = 9
      return draft
    })
    expect(calls).not.toContain('set')
    expect(calls).not.toContain('add')
    expect(calls).not.toContain('index')
    expect(result.map).not.toBe(source.map)
    expect(result.map).toBeInstanceOf(IndexedMap)
    expect(entries(result.map)).toEqual([['a', { v: 2 }]])
    expect(members(result.set)).toEqual([{ v: 2 }])
    expect(Object.hasOwn(result.array, 0)).toBe(true)
    expect([result.array[0], result.array[1]]).toEqual([5, 9])
  })

  it('are built and read back by reconcile with the built-in methods', () => {
    const next = sources()
    const current: Partial<ReturnType<typeof sources>> = {}
    reconcile(current, next)
    expect(calls.filter((call) => call !== 'entries' && call !== 'values')).toEqual([])
    expect(current.map).not.toBe(next.map)
    expect(current.map).toBeInstanceOf(IndexedMap)
    expect(entries(current.map!)).toEqual([['a', { v: 1 }]])
    expect(members(current.set!)).toEqual([{ v: 1 }])
    expect(Object.hasOwn(current.array!, 0)).toBe(true)
  })

  it('write a kept collection with the built-ins, never through its own methods', () => {
    const map = new IndexedMap<string, number>()
    map.set('a', 0)
    calls.length = 0
    const current = { map }
    reconcile(current, { map: new Map([['a', 1]]) })
    expect(current.map).toBe(map)
    expect(calls).toEqual([])
    expect(entries(map)).toEqual([['a', 1]])
  })
})
