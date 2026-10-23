import { OBJECT_KIND } from '../types/object'
import { ARRAY_KIND } from '../types/array'
import { TYPED_ARRAY_KIND } from '../types/typed-array'
import { ARRAY_BUFFER_KIND } from '../types/array-buffer'
import { DATE_KIND } from '../types/date'
import { MAP_KIND } from '../types/map'
import { SET_KIND } from '../types/set'
import { DATA_VIEW_KIND } from '../types/data-view'
import { describe, expect, it } from 'vitest'
import { capture } from '../publication/capture'
import { snapshot } from '../snapshot'
import { builtinTypes } from '../types/builtins'

describe('shared native graph capture', () => {
  it('registers every supported node once, including view construction edges', () => {
    const buffer = new ArrayBuffer(8)
    const source = {
      array: [] as unknown[],
      buffer,
      date: new Date(3),
      map: new Map(),
      set: new Set(),
      typed: new Uint16Array(buffer),
      view: new DataView(buffer),
    }
    source.array.push(source, source.typed)
    const graph = capture(builtinTypes, source)
    expect(graph.nodes.map((node) => node.layout.kind)).toEqual([
      OBJECT_KIND,
      ARRAY_KIND,
      TYPED_ARRAY_KIND,
      ARRAY_BUFFER_KIND,
      DATE_KIND,
      MAP_KIND,
      SET_KIND,
      DATA_VIEW_KIND,
    ])
    expect(graph.nodes[1].edges).toEqual([{ node: 0 }, { node: 2 }])
    expect(graph.nodes[2].edges).toEqual([{ node: 3 }])
    expect(graph.nodes[7].edges).toEqual([{ node: 3 }])
    expect(graph.nodes[0].edges[1]).toEqual({ node: 3 })
  })

  it('normalizes repeated observable collection keys without merging distinct objects', () => {
    const first = {}
    const second = {}
    const source = new Map<unknown, unknown>()
    source.entries = function* (): Generator<[unknown, unknown], undefined> {
      yield [first, 1]
      yield [second, 2]
      yield [first, 3]
      yield ['key', 4]
      yield ['key', 5]
      return undefined
    }
    source[Symbol.iterator] = source.entries.bind(source)
    const graph = capture(builtinTypes, source)
    expect(graph.nodes[0].edges).toEqual([{ node: 1 }, 3, { node: 2 }, 2, 'key', 5])
    expect(graph.nodes).toHaveLength(3)
  })

  it('trusts an existing snapshot memo entry without observing its source', () => {
    const source = {
      get value(): never {
        throw new Error('must not observe')
      },
    }
    const replacement = { arbitrary: true }
    expect(snapshot(source, new WeakMap([[source, replacement]]))).toBe(replacement)
    expect(snapshot(source, new WeakMap([[source, source]]))).toBe(source)
  })

  it('requires whole-source separation for trusted memo entries', () => {
    const left = new Date(0)
    const right = new Date(0)
    const source = [left, right]
    const swapped = snapshot(
      source,
      new WeakMap([
        [left, right],
        [right, left],
      ]),
    ) as Date[]
    expect(swapped).not.toBe(source)
    expect(swapped[0]).not.toBe(left)
    expect(swapped[1]).not.toBe(right)
    expect(swapped[0]).toBe(right)
    expect(swapped[1]).toBe(left)
    const detached = snapshot(source) as Date[]
    expect(detached.every((value) => !source.includes(value))).toBe(true)
    expect(detached[0]).not.toBe(detached[1])
  })

  it('preserves memo registration and completed-slot visibility during snapshot getters', () => {
    const seen = new WeakMap<object, object>()
    const child = { value: 1 }
    const source = {
      first: child,
      get later() {
        const current = seen.get(source) as { first: object }
        return [current.first === seen.get(child), seen.has(source)]
      },
    }
    const result = snapshot(source, seen)
    expect(result).toEqual({ first: { value: 1 }, later: [true, true] })
    expect(seen.get(source)).toBe(result)
  })

  it('copies a buffer once in snapshot mode, without calling an overriding slice', () => {
    let copies = 0
    class CountedBuffer extends ArrayBuffer {
      override slice(start: number, end?: number): ArrayBuffer {
        copies += 1
        return super.slice(start, end)
      }
    }
    const source = new CountedBuffer(8)
    new Uint8Array(source)[0] = 42
    const result = snapshot({ buffer: source, view: new DataView(source) }) as {
      buffer: ArrayBuffer
      view: DataView
    }
    expect(copies).toBe(0)
    expect(result.buffer).not.toBe(source)
    expect(result.buffer).toBeInstanceOf(CountedBuffer)
    expect(result.view.buffer).toBe(result.buffer)
    expect(result.view.getUint8(0)).toBe(42)
  })
  it('builds publication view samples with the built-in constructor', () => {
    const events: string[] = []
    class Sample extends Uint8Array {
      constructor(buffer: ArrayBuffer, offset: number, length: number) {
        super(buffer, offset, length)
        events.push('construct')
      }
    }
    const view = new Uint8Array(8)
    Object.defineProperty(view, 'constructor', { value: Sample })
    capture(builtinTypes, {
      view,
      get after() {
        events.push('after')
        return 1
      },
    })
    expect(events).toEqual(['after'])
  })

  it('preserves generated mixed graph identities and detaches their backing stores', () => {
    let seed = 1931
    const random = (size: number): number => {
      seed = (Math.imul(seed, 1_664_525) + 1_013_904_223) >>> 0
      return (seed >>> 8) % size
    }
    for (let fixture = 0; fixture < 200; fixture += 1) {
      const plain: Record<PropertyKey, unknown> = Object.create(null) as Record<
        PropertyKey,
        unknown
      >
      const array: unknown[] = new Array<unknown>(4)
      const map = new Map<object, object>()
      const set = new Set<object>()
      const buffer = new ArrayBuffer(8)
      const date = new Date(fixture % 2 === 0 ? fixture : Number.NaN)
      const view = new DataView(buffer, 2, 4)
      const typed = new Uint16Array(buffer, 2, 2)
      const nodes: object[] = [plain, array, map, set, buffer, date, view, typed]
      const symbol = Symbol('slot')
      plain.a = nodes[random(nodes.length)]
      plain[symbol] = nodes[random(nodes.length)]
      array[1] = nodes[random(nodes.length)]
      for (let slot = 0; slot < 4; slot += 1) {
        map.set(nodes[random(nodes.length)], nodes[random(nodes.length)])
        set.add(nodes[random(nodes.length)])
      }
      new Uint8Array(buffer)[0] = fixture
      const copied = snapshot(nodes) as typeof nodes
      const lookup = (value: unknown): unknown => copied[nodes.indexOf(value as object)]
      expect(new Set(copied).size).toBe(nodes.length)
      expect(copied.every((node) => !nodes.includes(node))).toBe(true)
      const copiedPlain = copied[0] as typeof plain
      expect(Object.getPrototypeOf(copiedPlain)).toBeNull()
      expect(Reflect.ownKeys(copiedPlain)).toEqual(['a', symbol])
      expect(copiedPlain.a).toBe(lookup(plain.a))
      expect(copiedPlain[symbol]).toBe(lookup(plain[symbol]))
      const copiedArray = copied[1] as unknown[]
      expect(copiedArray).toHaveLength(4)
      expect(Object.keys(copiedArray)).toEqual(['1'])
      expect(copiedArray[1]).toBe(lookup(array[1]))
      expect([...(copied[2] as Map<object, object>)]).toEqual(
        [...map].map(([key, value]) => [lookup(key), lookup(value)]),
      )
      expect([...(copied[3] as Set<object>)]).toEqual([...set].map(lookup))
      expect((copied[5] as Date).getTime()).toBe(date.getTime())
      expect((copied[6] as DataView).buffer).toBe(copied[4])
      expect((copied[7] as Uint16Array).buffer).toBe(copied[4])
      expect((copied[6] as DataView).byteOffset).toBe(2)
      expect((copied[7] as Uint16Array).length).toBe(2)
      new Uint8Array(copied[4] as ArrayBuffer)[0] = 255
      expect(new Uint8Array(buffer)[0]).toBe(fixture)
    }
  })
  it.each(['snapshot', 'publication'])(
    'closes native collection iterators after a child throws (%s)',
    (mode) => {
      const failure = new Error('child observation failed')
      let closed = 0
      const source = new Map<unknown, unknown>()
      source.entries = function* (): Generator<[unknown, unknown], undefined> {
        try {
          yield [
            0,
            {
              get bad() {
                throw failure
              },
            },
          ]
        } finally {
          closed += 1
        }
        return undefined
      }
      source[Symbol.iterator] = source.entries.bind(source)
      expect(() =>
        mode === 'snapshot' ? snapshot(source) : capture(builtinTypes, source),
      ).toThrow(failure)
      expect(closed).toBe(1)
    },
  )
  it('canonicalizes signed-zero keys in the captured collection payload', () => {
    const map = new Map<unknown, unknown>()
    map[Symbol.iterator] = function* (): Generator<[unknown, unknown], undefined> {
      yield [0, 1]
      yield [-0, 2]
      return undefined
    }
    const set = new Set<unknown>()
    set[Symbol.iterator] = function* (): Generator<unknown, undefined> {
      yield -0
      return undefined
    }
    const mapEdges = capture(builtinTypes, map).nodes[0].edges
    const setEdges = capture(builtinTypes, set).nodes[0].edges
    expect(mapEdges).toEqual([0, 2])
    expect(setEdges).toEqual([0])
    expect(Object.is(mapEdges[0], 0) && Object.is(setEdges[0], 0)).toBe(true)
  })
  it('normalizes snapshot collections through native writes, including repeated observed keys', () => {
    const key = { id: 1 }
    const map = new Map<unknown, unknown>()
    map.entries = function* () {
      yield [key, 1]
      yield [key, 2]
      yield [-0, 3]
      yield [0, 4]
      return undefined
    }
    const set = new Set<unknown>()
    set.values = function* () {
      yield key
      yield key
      yield -0
      yield 0
      return undefined
    }
    const result = snapshot({ key, map, set }) as {
      key: object
      map: Map<unknown, unknown>
      set: Set<unknown>
    }
    expect([...result.map]).toEqual([
      [result.key, 2],
      [0, 4],
    ])
    expect([...result.set]).toEqual([result.key, 0])
    expect(result.key).not.toBe(key)
  })

  it('extends snapshot arrays through observed writes after live length changes', () => {
    const source: unknown[] = new Array(2)
    Object.defineProperty(source, 0, {
      get() {
        source[4] = 'last'
        return 'first'
      },
    })
    const result = snapshot(source) as unknown[]
    expect(result.length).toBe(5)
    expect(Object.keys(result)).toEqual(['0', '4'])
    expect(result[0]).toBe('first')
    expect(result[4]).toBe('last')
  })
})
