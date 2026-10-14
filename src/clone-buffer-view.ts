import { copyDataView } from './types/data-view'
import { copyTypedArray } from './types/typed-array'

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
export const cloneBufferView = <T extends ArrayBufferView>(value: T, buffer: ArrayBuffer): T =>
  (value instanceof DataView ? copyDataView(value, buffer) : copyTypedArray(value, buffer)) as T
