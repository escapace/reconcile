import type { DeserializeOptions } from './deserialize'
import { measureGraph as measure } from './serialization/decode'
import { maxBytesOf } from './serialization/size'

/**
 * Returns the smallest `maxBytes` with which {@link deserialize} accepts JSON data.
 *
 * @remarks
 * `requiredMaxBytes` checks and counts `json` as {@link deserialize} does under a finite
 * `maxBytes`, without restoring the value or modifying `json`. For data that {@link serialize}
 * produces, the result is the size of the restored value. For other data it can be larger, for
 * example when a `Map` key is repeated. The result is `Infinity` when the size is larger than every
 * finite `maxBytes`, which requires `maxBytes: Infinity`.
 *
 * For data that meets the requirements of `deserialize`, `deserialize` with a finite `maxBytes`
 * returns if and only if `maxBytes` is at least the result. The exceptions: `Object.prototype` or
 * `Array.prototype` has a getter, setter or read-only property at an array index; a built-in method
 * is replaced; or `deserialize` throws a native error, for example for a `Map` or `Set` larger than
 * the engine allows.
 *
 * Measuring creates each `Date`, `bigint`, view, `URL`, `URLSearchParams`, Temporal value and
 * sparse array in the data, and allocates a buffer for each `ArrayBuffer`; `options.maxBytes`
 * bounds that work as it bounds `deserialize`. Use `maxBytes: Infinity` only for trusted data, such
 * as the output of `serialize`: measuring data that does not come from `JSON.parse` or `serialize`
 * can fail to finish when it contains a cycle. Unlike `deserialize`, `requiredMaxBytes` rejects a
 * value that `JSON.parse` cannot produce, such as `undefined`, even under `Infinity`.
 *
 * @example
 * ```ts
 * const value = { name: 'Ada', tags: ['a', 'b'] }
 * const maxBytes = requiredMaxBytes(serialize(value), { maxBytes: Infinity }) // 112
 * deserialize(serialize(value), { maxBytes }) // restores the value
 * deserialize(serialize(value), { maxBytes: maxBytes - 1 }) // throws DeserializeLimitExceeded
 * ```
 *
 * @param json - JSON data, as for {@link deserialize}. It is not modified.
 * @param options - The largest result to measure up to; see {@link DeserializeOptions}.
 * @returns The smallest `maxBytes` that `deserialize` accepts for `json`: a multiple of 8, or
 * `Infinity`.
 * @throws {@link ReconcileError} with type `DeserializeLimitInvalid` when `maxBytes` is invalid,
 * `DeserializeLimitExceeded` when the result would be larger than `maxBytes`, or
 * `DeserializeInputInvalid` when `json` is not in the format that `serialize` produces.
 * @throws Native constructor or allocation errors, unchanged.
 */
export function requiredMaxBytes(json: unknown, options: DeserializeOptions): number {
  const bytes = 8 * measure(json, maxBytesOf(options))
  // Size.lean accepts_iff_bytes. A finite limit is a safe integer, so above the largest one only
  // Infinity is accepted.
  return bytes <= Number.MAX_SAFE_INTEGER ? bytes : Infinity
}
