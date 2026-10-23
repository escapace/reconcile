import { describe, expect, it } from 'vitest'
import { snapshot } from '../index'

// The built-in snapshot walk observes Date, ArrayBuffer and view kinds inline. These cases pin
// the facet behaviour it repeats, including the construction answer a view's buffer edge gets.
describe('snapshot binary and Date observation', () => {
  it('reads a view through the built-in accessors, not its own or overriding properties', () => {
    let reads = 0
    const buffer = new ArrayBuffer(8)
    new Uint8Array(buffer).set([1, 2, 3, 4, 5, 6, 7, 8])
    const typed = new Uint16Array(buffer, 2, 2)
    const view = new DataView(buffer, 1, 3)
    const counted = {
      get() {
        reads += 1
        return 1
      },
    }
    for (const value of [typed, view])
      for (const key of ['buffer', 'byteOffset', 'byteLength', 'length', 'constructor'])
        Object.defineProperty(value, key, counted)
    const copy = snapshot({ buffer, typed, view }) as {
      buffer: ArrayBuffer
      typed: Uint16Array
      view: DataView
    }
    expect(reads).toBe(0)
    const typedBuffer = Reflect.get(Uint16Array.prototype, 'buffer', copy.typed) as unknown
    const viewBuffer = Reflect.get(DataView.prototype, 'buffer', copy.view) as unknown
    expect(typedBuffer).toBe(copy.buffer)
    expect(viewBuffer).toBe(copy.buffer)
    expect(copy.buffer).not.toBe(buffer)
    expect(Array.from(new Uint8Array(copy.buffer))).toEqual([1, 2, 3, 4, 5, 6, 7, 8])
    expect(Reflect.get(Uint16Array.prototype, 'byteOffset', copy.typed)).toBe(2)
    expect(Reflect.get(Uint16Array.prototype, 'length', copy.typed)).toBe(2)
    expect(Reflect.get(DataView.prototype, 'byteOffset', copy.view)).toBe(1)
    expect(Reflect.get(DataView.prototype, 'byteLength', copy.view)).toBe(3)
  })

  it('copies a typed-array subclass without running its constructor', () => {
    let runs = 0
    class Tagged extends Uint8Array {
      tag = 'field'
      constructor(...parameters: [number]) {
        super(...parameters)
        runs += 1
      }
    }
    const source = new Tagged(3)
    source[1] = 7
    runs = 0
    const copy = snapshot({ source }) as { source: Tagged }
    expect(runs).toBe(0)
    expect(copy.source).toBeInstanceOf(Tagged)
    expect(Object.keys(copy.source)).toEqual(['0', '1', '2'])
    expect(Array.from(copy.source)).toEqual([0, 7, 0])
  })

  it('builds a view over the caller memo entry for its buffer', () => {
    const buffer = new ArrayBuffer(4)
    const mapped = new ArrayBuffer(8)
    const copy = snapshot([new DataView(buffer, 1, 2)], new WeakMap([[buffer, mapped]])) as [
      DataView,
    ]
    expect(copy[0].buffer).toBe(mapped)
    expect([copy[0].byteOffset, copy[0].byteLength]).toEqual([1, 2])
  })

  it('copies a buffer without calling an own slice or the constructor, keeping its prototype', () => {
    let calls = 0
    class Counted extends ArrayBuffer {
      constructor(length: number) {
        super(length)
        calls += 1
      }
    }
    const buffer = new Counted(4)
    new Uint8Array(buffer)[3] = 9
    Object.defineProperty(buffer, 'slice', {
      value: () => {
        calls += 1
        return new ArrayBuffer(2)
      },
    })
    calls = 0
    const copy = snapshot({ buffer }) as { buffer: ArrayBuffer }
    expect(calls).toBe(0)
    expect(copy.buffer).toBeInstanceOf(Counted)
    expect(Array.from(new Uint8Array(copy.buffer))).toEqual([0, 0, 0, 9])
  })

  it('copies a Date by its built-in time without reading an own getTime', () => {
    const date = new Date(9)
    let reads = 0
    Object.defineProperty(date, 'getTime', {
      value: () => {
        reads += 1
        return 42
      },
    })
    const copy = snapshot([date, date]) as [Date, Date]
    expect(reads).toBe(0)
    expect(copy[0]).toBe(copy[1])
    expect(copy[0]).not.toBe(date)
    expect(Date.prototype.getTime.call(copy[0])).toBe(9)
  })
})
