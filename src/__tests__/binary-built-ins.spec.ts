import { describe, expect, it } from 'vitest'
import { produce, reconcile, snapshot } from '../index'

const bytes = (value: ArrayBufferView): number[] =>
  Array.from(new Uint8Array(value.buffer, value.byteOffset, value.byteLength))

describe('buffers and views across functions', () => {
  it('copies a changed typed-array subclass in produce without running its constructor', () => {
    let runs = 0
    class Tagged extends Uint8Array {
      constructor(...parameters: [number]) {
        super(...parameters)
        runs += 1
      }
    }
    const current = { data: new Tagged(3) }
    runs = 0
    const result = produce(current, (draft) => {
      draft.data[0] = 5
      return draft
    })
    expect(runs).toBe(0)
    expect(result.data).toBeInstanceOf(Tagged)
    expect(result.data).not.toBe(current.data)
    expect(Array.from(result.data)).toEqual([5, 0, 0])
    expect(Array.from(current.data)).toEqual([0, 0, 0])
  })

  it('copies a new typed-array subclass in reconcile without running its constructor', () => {
    let runs = 0
    class Tagged extends Uint8Array {
      constructor(...parameters: [number]) {
        super(...parameters)
        runs += 1
      }
    }
    const next = { data: new Tagged(2) }
    next.data[1] = 4
    runs = 0
    const current: { data?: Uint8Array } = {}
    reconcile(current, next)
    expect(runs).toBe(0)
    expect(current.data).toBeInstanceOf(Tagged)
    expect(current.data).not.toBe(next.data)
    expect(Array.from(current.data!)).toEqual([0, 4])
  })

  it('compares views by their built-in shape, not an own constructor or length', () => {
    const current = { data: new Uint8Array(2) }
    const kept = current.data
    const next = { data: new Uint8Array([1, 2]) }
    Object.defineProperty(next.data, 'constructor', { value: Int8Array })
    Object.defineProperty(next.data, 'byteLength', { value: 99 })
    reconcile(current, next)
    expect(current.data).toBe(kept)
    expect(Array.from(kept)).toEqual([1, 2])
  })
})

describe('SharedArrayBuffer', () => {
  it('is kept by reference, and a view over one is copied over the same buffer', () => {
    const shared = new SharedArrayBuffer(4)
    const view = new Uint8Array(shared, 1, 2)
    view[0] = 9
    // Either value may be met first.
    const [first, second] = snapshot([shared, view]) as [SharedArrayBuffer, Uint8Array]
    const [third, fourth] = snapshot([view, shared]) as [Uint8Array, SharedArrayBuffer]
    for (const [buffer, copy] of [
      [first, second],
      [fourth, third],
    ] as const) {
      expect(buffer).toBe(shared)
      expect(copy).not.toBe(view)
      expect(copy.buffer).toBe(shared)
      expect([copy.byteOffset, copy.length]).toEqual([1, 2])
    }
  })

  it('is read as itself in produce, so writes through a view reach the shared memory', () => {
    const shared = new SharedArrayBuffer(2)
    const current = { count: 0, shared, view: new Uint8Array(shared) }
    const result = produce(current, (draft) => {
      expect(draft.shared).toBe(shared)
      expect(draft.view.buffer).toBe(shared)
      draft.view[1] = 3
      draft.count = 1
      return draft
    })
    expect(result.shared).toBe(shared)
    expect(result.view).toBe(current.view)
    expect(bytes(current.view)).toEqual([0, 3])
  })

  it('is assigned by reconcile, and a view over another buffer is replaced', () => {
    const shared = new SharedArrayBuffer(2)
    new Uint8Array(shared)[0] = 7
    const current = {
      other: new Uint8Array(new SharedArrayBuffer(2)),
      plain: new Uint8Array(2),
      same: new Uint8Array(shared),
      shared: new SharedArrayBuffer(2),
    }
    const { other, plain, same } = current
    reconcile(current, {
      other: new Uint8Array(shared),
      plain: new Uint8Array(shared),
      same: new Uint8Array(shared),
      shared,
    })
    expect(current.shared).toBe(shared)
    expect(current.same).toBe(same)
    for (const view of [current.other, current.plain]) {
      expect(view).not.toBe(other)
      expect(view).not.toBe(plain)
      expect(view.buffer).toBe(shared)
      expect(bytes(view)).toEqual([7, 0])
    }
  })

  it('leaves a view over a SharedArrayBuffer to a plain buffer copy in reconcile', () => {
    const current = { view: new Uint8Array(new SharedArrayBuffer(2)) }
    const previous = current.view
    reconcile(current, { view: new Uint8Array([4, 5]) })
    expect(current.view).not.toBe(previous)
    expect(current.view.buffer).toBeInstanceOf(ArrayBuffer)
    expect(Array.from(current.view)).toEqual([4, 5])
  })
})

/* eslint-disable baseline-js/use-baseline -- resizable buffers, on engines that have them */
describe('resizable buffers', () => {
  it('are copied as resizable buffers with the same maximum', () => {
    const buffer = new ArrayBuffer(2, { maxByteLength: 8 })
    new Uint8Array(buffer)[1] = 5
    const copy = snapshot({ buffer }) as { buffer: ArrayBuffer }
    const result = produce({ buffer, view: new Uint8Array(buffer) }, (draft) => {
      draft.view[0] = 9
      return draft
    })
    const current: { buffer?: ArrayBuffer } = {}
    reconcile(current, { buffer })
    for (const [value, bytes] of [
      [copy.buffer, [0, 5]],
      [result.buffer, [9, 5]],
      [current.buffer!, [0, 5]],
    ] as const) {
      expect(value).not.toBe(buffer)
      expect([value.resizable, value.maxByteLength]).toEqual([true, 8])
      expect(Array.from(new Uint8Array(value))).toEqual(bytes)
    }
    expect(result.view.buffer).toBe(result.buffer)
    expect((snapshot(new ArrayBuffer(1)) as ArrayBuffer).resizable).toBe(false)
  })

  it('are kept by reconcile only for a buffer of the same resizability and maximum', () => {
    for (const [held, wanted] of [
      [new ArrayBuffer(2, { maxByteLength: 8 }), new ArrayBuffer(2)],
      [new ArrayBuffer(2), new ArrayBuffer(2, { maxByteLength: 8 })],
      [new ArrayBuffer(2, { maxByteLength: 8 }), new ArrayBuffer(2, { maxByteLength: 4 })],
    ]) {
      const current = { buffer: held }
      reconcile(current, { buffer: wanted })
      expect(current.buffer).not.toBe(held)
      expect([current.buffer.resizable, current.buffer.maxByteLength]).toEqual([
        wanted.resizable,
        wanted.maxByteLength,
      ])
    }
    const kept = new ArrayBuffer(2, { maxByteLength: 8 })
    const current = { buffer: kept }
    const wanted = new ArrayBuffer(2, { maxByteLength: 8 })
    new Uint8Array(wanted)[0] = 3
    reconcile(current, { buffer: wanted })
    expect(current.buffer).toBe(kept)
    expect(Array.from(new Uint8Array(kept))).toEqual([3, 0])
  })
})
/* eslint-enable baseline-js/use-baseline */
