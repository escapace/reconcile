/**
 * Recreates a `DataView` or typed-array view over a supplied buffer.
 *
 * @remarks
 * The returned view preserves the source view's constructor, byte offset, and visible range while
 * switching the backing store to `buffer`. This helper does not copy bytes. Callers must pass a
 * backing `ArrayBuffer` whose contents already represent the desired result and whose size and
 * alignment are compatible with `value`'s constructor, `byteOffset`, and visible range.
 *
 * @param value - Source view whose constructor and range metadata are reused.
 * @param buffer - Backing buffer for the recreated view.
 * @returns A distinct view over `buffer` with the same observable shape as `value`.
 * @throws When `buffer` is not large enough or not properly aligned for the source view's
 * constructor, offset, and length.
 * @internal
 */
export const cloneBufferView = <T extends ArrayBufferView>(value: T, buffer: ArrayBuffer): T => {
  if (value instanceof DataView) {
    return new DataView(buffer, value.byteOffset, value.byteLength) as unknown as T
  }

  const typedArray = value as unknown as {
    byteOffset: number
    constructor: new (buffer_: ArrayBuffer, byteOffset_: number, length_: number) => T
    length: number
  }

  return new typedArray.constructor(buffer, typedArray.byteOffset, typedArray.length)
}
