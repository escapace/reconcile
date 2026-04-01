import { assert, describe, it } from 'vitest'

import { cloneBufferView } from '../clone-buffer-view'

type TypedArrayInstance =
  | BigInt64Array
  | BigUint64Array
  | Float32Array
  | Float64Array
  | Int16Array
  | Int32Array
  | Int8Array
  | Uint16Array
  | Uint32Array
  | Uint8Array
  | Uint8ClampedArray

interface TypedArrayConstructor<T extends TypedArrayInstance = TypedArrayInstance> {
  readonly BYTES_PER_ELEMENT: number
  readonly name: string
  new (buffer: ArrayBuffer, byteOffset: number, length: number): T
}

const typedArrayConstructors = [
  Int8Array,
  Uint8Array,
  Uint8ClampedArray,
  Int16Array,
  Uint16Array,
  Int32Array,
  Uint32Array,
  Float32Array,
  Float64Array,
  BigInt64Array,
  BigUint64Array,
] as const satisfies readonly TypedArrayConstructor[]

const fillBuffer = (buffer: ArrayBuffer, start: number): void => {
  const bytes = new Uint8Array(buffer)

  for (let index = 0; index < bytes.length; index += 1) {
    bytes[index] = (start + index) % 256
  }
}

const visibleBytes = (value: ArrayBufferView): number[] =>
  Array.from(new Uint8Array(value.buffer, value.byteOffset, value.byteLength))

describe('cloneBufferView', () => {
  describe('DataView', () => {
    it('clones a subview onto the supplied buffer while preserving offset and length', () => {
      const sourceBuffer = new ArrayBuffer(12)
      const targetBuffer = new ArrayBuffer(12)
      fillBuffer(sourceBuffer, 1)
      fillBuffer(targetBuffer, 101)

      const source = new DataView(sourceBuffer, 3, 5)
      const result = cloneBufferView(source, targetBuffer)

      assert.notEqual(result, source)
      assert.instanceOf(result, DataView)
      assert.equal(result.buffer, targetBuffer)
      assert.equal(result.byteOffset, 3)
      assert.equal(result.byteLength, 5)
      assert.deepEqual(visibleBytes(result), [104, 105, 106, 107, 108])
      assert.deepEqual(visibleBytes(source), [4, 5, 6, 7, 8])
    })

    it('supports zero-length DataViews at the end of the buffer', () => {
      const sourceBuffer = new ArrayBuffer(8)
      const targetBuffer = new ArrayBuffer(8)
      fillBuffer(sourceBuffer, 1)
      fillBuffer(targetBuffer, 101)

      const source = new DataView(sourceBuffer, 8, 0)
      const result = cloneBufferView(source, targetBuffer)

      assert.notEqual(result, source)
      assert.equal(result.buffer, targetBuffer)
      assert.equal(result.byteOffset, 8)
      assert.equal(result.byteLength, 0)
      assert.deepEqual(visibleBytes(result), [])
    })

    it('returns a distinct DataView even when reusing the same buffer', () => {
      const buffer = new ArrayBuffer(10)
      fillBuffer(buffer, 21)

      const source = new DataView(buffer, 2, 6)
      const result = cloneBufferView(source, buffer)

      assert.notEqual(result, source)
      assert.equal(result.buffer, buffer)
      assert.equal(result.byteOffset, 2)
      assert.equal(result.byteLength, 6)
      assert.deepEqual(visibleBytes(result), visibleBytes(source))
    })
  })

  describe('typed arrays', () => {
    for (const Ctor of typedArrayConstructors) {
      it(`clones ${Ctor.name} subviews onto the supplied buffer`, () => {
        const byteOffset = Ctor.BYTES_PER_ELEMENT * 2
        const length = 3
        const byteLength = byteOffset + length * Ctor.BYTES_PER_ELEMENT + Ctor.BYTES_PER_ELEMENT
        const sourceBuffer = new ArrayBuffer(byteLength)
        const targetBuffer = new ArrayBuffer(byteLength)
        fillBuffer(sourceBuffer, 1)
        fillBuffer(targetBuffer, 101)

        const source = new Ctor(sourceBuffer, byteOffset, length)
        const result = cloneBufferView(source, targetBuffer)

        assert.notEqual(result, source)
        assert.equal(result.constructor, Ctor)
        assert.equal(result.buffer, targetBuffer)
        assert.equal(result.byteOffset, byteOffset)
        assert.equal(result.byteLength, length * Ctor.BYTES_PER_ELEMENT)
        assert.equal(result.length, length)
        assert.deepEqual(
          visibleBytes(result),
          Array.from(new Uint8Array(targetBuffer, byteOffset, length * Ctor.BYTES_PER_ELEMENT)),
        )
        assert.deepEqual(
          visibleBytes(source),
          Array.from(new Uint8Array(sourceBuffer, byteOffset, length * Ctor.BYTES_PER_ELEMENT)),
        )
      })

      it(`supports zero-length ${Ctor.name} views at the end of the buffer`, () => {
        const byteOffset = Ctor.BYTES_PER_ELEMENT * 4
        const sourceBuffer = new ArrayBuffer(byteOffset)
        const targetBuffer = new ArrayBuffer(byteOffset)
        fillBuffer(sourceBuffer, 1)
        fillBuffer(targetBuffer, 101)

        const source = new Ctor(sourceBuffer, byteOffset, 0)
        const result = cloneBufferView(source, targetBuffer)

        assert.notEqual(result, source)
        assert.equal(result.constructor, Ctor)
        assert.equal(result.buffer, targetBuffer)
        assert.equal(result.byteOffset, byteOffset)
        assert.equal(result.byteLength, 0)
        assert.equal(result.length, 0)
        assert.deepEqual(visibleBytes(result), [])
      })

      it(`returns a distinct ${Ctor.name} instance even when reusing the same buffer`, () => {
        const byteOffset = Ctor.BYTES_PER_ELEMENT
        const length = 2
        const buffer = new ArrayBuffer(byteOffset + length * Ctor.BYTES_PER_ELEMENT)
        fillBuffer(buffer, 33)

        const source = new Ctor(buffer, byteOffset, length)
        const result = cloneBufferView(source, buffer)

        assert.notEqual(result, source)
        assert.equal(result.constructor, Ctor)
        assert.equal(result.buffer, buffer)
        assert.equal(result.byteOffset, byteOffset)
        assert.equal(result.byteLength, length * Ctor.BYTES_PER_ELEMENT)
        assert.equal(result.length, length)
        assert.deepEqual(visibleBytes(result), visibleBytes(source))
      })
    }
  })
})
