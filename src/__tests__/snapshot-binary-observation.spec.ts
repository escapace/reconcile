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

// A typed array that covers a fixed-length buffer the walk has not met is copied from itself; the
// buffer's copy is that copy's buffer, read when the buffer or another view needs it.
/* eslint-disable baseline-js/use-baseline -- resizable buffers, on engines that have them */
describe('snapshot of a typed array met before its buffer', () => {
  it('shares the buffer of its copy with the buffer and the views met after it', () => {
    const buffer = new ArrayBuffer(8)
    new Uint8Array(buffer).set([1, 2, 3, 4, 5, 6, 7, 8])
    const copy = snapshot({
      array: new Uint16Array(buffer),
      buffer,
      data: new DataView(buffer, 2, 4),
      part: new Uint8Array(buffer, 4),
    }) as { array: Uint16Array; buffer: ArrayBuffer; data: DataView; part: Uint8Array }
    expect(copy.array.buffer).toBe(copy.buffer)
    expect(copy.data.buffer).toBe(copy.buffer)
    expect(copy.part.buffer).toBe(copy.buffer)
    expect(copy.buffer).not.toBe(buffer)
    expect(Object.getPrototypeOf(copy.buffer)).toBe(ArrayBuffer.prototype)
    expect(copy.buffer.resizable).toBe(false)
    expect(Array.from(new Uint8Array(copy.buffer))).toEqual([1, 2, 3, 4, 5, 6, 7, 8])
    expect([copy.data.byteOffset, copy.data.byteLength]).toEqual([2, 4])
    expect([copy.part.byteOffset, copy.part.length]).toEqual([4, 4])
  })

  it('keeps the bytes the array held when it was copied', () => {
    const typed = new Uint8Array([1, 2, 3])
    const copy = snapshot({ typed }) as { typed: Uint8Array }
    typed[0] = 9
    copy.typed[1] = 8
    expect(Array.from(new Uint8Array(copy.typed.buffer))).toEqual([1, 8, 3])
    expect(Array.from(typed)).toEqual([9, 2, 3])
  })

  it('records the copy of its buffer in the caller memo', () => {
    const typed = new Float64Array([1.5, 2.5])
    const seen = new WeakMap<object, object>()
    const copy = snapshot({ typed }, seen) as { typed: Float64Array }
    expect(seen.get(typed)).toBe(copy.typed)
    expect(seen.get(typed.buffer)).toBe(copy.typed.buffer)
    expect(Array.from(copy.typed)).toEqual([1.5, 2.5])
  })

  it('copies the whole buffer of an array over part of it or over a resizable one', () => {
    const part = new Uint8Array(new ArrayBuffer(8), 2, 4)
    const resizable = new ArrayBuffer(4, { maxByteLength: 16 })
    new Uint8Array(resizable).set([1, 2, 3, 4])
    const copy = snapshot({ growing: new Uint16Array(resizable), part }) as {
      growing: Uint16Array
      part: Uint8Array
    }
    expect(copy.part.buffer.byteLength).toBe(8)
    expect([copy.part.byteOffset, copy.part.length]).toEqual([2, 4])
    expect(copy.growing.buffer.resizable).toBe(true)
    expect(copy.growing.buffer.maxByteLength).toBe(16)
    expect(Array.from(new Uint8Array(copy.growing.buffer))).toEqual([1, 2, 3, 4])
  })
})
/* eslint-enable baseline-js/use-baseline */
