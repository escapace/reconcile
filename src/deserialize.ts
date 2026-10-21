import { decodeGraph as decode } from './serialization/decode'
import { maxBytesOf } from './serialization/size'

/** Options for {@link deserialize}. */
export interface DeserializeOptions {
  /**
   * The largest size, in bytes, of the value `deserialize` may return: a non-negative safe integer,
   * or `Infinity` for trusted input only. Each object counts once, however often it is referenced,
   * and each primitive counts at every occurrence.
   */
  readonly maxBytes: number
}

/**
 * Restores a value from JSON data produced by {@link serialize}.
 *
 * @remarks
 * Shared references and cycles are restored. For data that `serialize` produces, every object in
 * the result is mutable and distinct from the original value's objects, every property except an
 * array's `length` is a writable, enumerable and configurable data property, and a `__proto__` key
 * is an own data property. A repeated `Map` key keeps its first position and last value, and a
 * repeated `Set` member keeps its first position, as with native insertion. Callers must not modify
 * standard built-ins or prototypes during the call.
 *
 * Pass the result of `JSON.parse` or {@link serialize} directly, and do not use it after the call,
 * whether the call returns or throws: `deserialize` can modify `json`, and the result can share
 * arrays and objects with it. To retry, parse the text again. Data that does not come from
 * `JSON.parse` or `serialize` must contain only plain arrays without extra properties and plain
 * objects with only data properties, and must not contain the same array at more than one place.
 * Under a finite `maxBytes`, a value of a type that `JSON.parse` cannot produce, such as
 * `undefined`, a typed array, a `Map` or a `bigint`, is rejected. The data carries no format
 * version: both sides must use the same version of this library.
 *
 * @example
 * ```ts
 * const user = { name: 'Ada' }
 * const text = JSON.stringify(serialize({ owner: user, members: [user] }))
 * const copy = deserialize(JSON.parse(text), { maxBytes: 1_000_000 }) as {
 *   owner: object
 *   members: object[]
 * }
 * // copy.owner === copy.members[0]; copy.owner !== user
 * ```
 *
 * @param json - JSON data produced by {@link serialize} of the same library version. The call can
 * modify it; do not use it afterwards.
 * @param options - The size limit; see {@link DeserializeOptions}.
 * @returns The restored value.
 * @throws {@link ReconcileError} with type `DeserializeLimitInvalid` when `maxBytes` is invalid,
 * `DeserializeLimitExceeded` when the value would be larger than `maxBytes`, or
 * `DeserializeInputInvalid` when `json` is not in the format that `serialize`
 * produces.
 * @throws Native constructor or allocation errors, unchanged.
 */
export function deserialize(json: unknown, options: DeserializeOptions): unknown {
  return decode(json, maxBytesOf(options))
}
