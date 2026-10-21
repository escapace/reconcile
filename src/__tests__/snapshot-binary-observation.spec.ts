import { describe, expect, it } from 'vitest'
import { snapshot } from '../index'

// The built-in snapshot walk observes Date, ArrayBuffer and view kinds inline. These cases pin
// the facet behaviour it repeats, including the construction answer a view's buffer edge gets.
describe('snapshot binary and Date observation', () => {
  it('answers a view whose buffer getter returns the pending view itself', () => {
    const view = new Uint8Array(4)
    Object.defineProperty(view, 'buffer', { get: () => view })
    const copy = snapshot({ view }) as { view: Uint8Array }
    expect(copy.view).toBeInstanceOf(Uint8Array)
    expect(copy.view).not.toBe(view)
    expect(copy.view.length).toBe(0)
  })

  it('answers a buffer edge that reaches copied search parameters with their URL carrier', () => {
    const url = new URL('https://a.test/?a=1&b=2')
    const view = new Uint8Array(2)
    Object.defineProperty(view, 'buffer', { get: () => url.searchParams })
    const copy = snapshot({ url, view }) as { view: Uint8Array }
    // A copy of the parameters is iterable and would give two elements; the carrier gives none.
    expect(copy.view.length).toBe(0)
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

  it('uses the result of an own slice method as the buffer copy', () => {
    const buffer = new ArrayBuffer(4)
    const shared = new ArrayBuffer(2)
    Object.defineProperty(buffer, 'slice', { value: () => shared })
    expect(() => snapshot({ buffer, view: new DataView(buffer) })).toThrow(RangeError)
    const copy = snapshot({ buffer, other: shared }) as { buffer: ArrayBuffer; other: ArrayBuffer }
    expect(copy.buffer).toBe(shared)
  })

  it('reads an own getTime once per Date identity', () => {
    const date = new Date(9)
    let reads = 0
    Object.defineProperty(date, 'getTime', {
      value: () => {
        reads += 1
        return 42
      },
    })
    const copy = snapshot([date, date]) as [Date, Date]
    expect(reads).toBe(1)
    expect(copy[0]).toBe(copy[1])
    expect(copy[0]).not.toBe(date)
    expect(Date.prototype.getTime.call(copy[0])).toBe(42)
  })

  it('passes a primitive or an earlier copy from a buffer getter to the view constructor', () => {
    const numeric = new Uint8Array(4)
    Object.defineProperty(numeric, 'buffer', { get: () => 3 })
    expect((snapshot({ numeric }) as { numeric: Uint8Array }).numeric.length).toBe(3)
    const array = [5, 6]
    const view = new Uint8Array(2)
    Object.defineProperty(view, 'buffer', { get: () => array })
    expect(Array.from((snapshot([array, view]) as [number[], Uint8Array])[1])).toEqual([5, 6])
  })
})
