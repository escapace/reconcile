import type { Budget, DecodeContext } from './contracts'
import { deserializeLimitExceeded, deserializeLimitInvalid } from '../error'
import { decodeFail as fail } from './common'
// Size.lean: a value's size in 64-bit words, with every object stored once and every primitive
// stored where it occurs. Charges are never negative, so the first running total above the limit
// decides (stops_iff); `deserialize` rejects when 8 bytes per word exceed `maxBytes`.
export function charge(context: Budget, words: number): void {
  if ((context.words += words) > context.limit) exceeded(context)
}
// `maxBytes`, read once: a non-negative safe integer or Infinity.
export function maxBytesOf(options: { readonly maxBytes: number } | undefined): number {
  const maxBytes = options?.maxBytes
  if (maxBytes !== Infinity && (!Number.isSafeInteger(maxBytes) || maxBytes! < 0))
    throw deserializeLimitInvalid(maxBytes)
  return maxBytes!
}
// Kept apart so that `charge` stays small enough to inline.
function exceeded(context: Budget): never {
  throw deserializeLimitExceeded(context.maxBytes)
}
// Size.lean stringWords: four 16-bit code units per word.
export const stringWords = (length: number): number => (length + 3) >>> 2
// Size.lean words: a literal is any JSON value, charged where it occurs: a string's payload, or
// an object's header, slots, keys and contents. Under a limit a literal must be JSON data, as
// JSON.parse produces it: a typed array, Map, bigint or function passed in its place is
// rejected before it is read. The walk charges as it goes, so it stops at the limit even on a
// caller-built cyclic value.
export function chargeLiteral(context: Budget, literal: unknown): void {
  const pending: object[] = []
  chargeItem(context, literal, pending)
  while (pending.length !== 0) chargeObject(context, pending.pop()!, pending)
}
function chargeItem(context: Budget, item: unknown, pending: object[]): void {
  switch (typeof item) {
    case 'boolean':
    case 'number':
      return
    case 'object':
      if (item !== null) pending.push(item)
      return
    case 'string':
      charge(context, stringWords(item.length))
      return
    default:
      fail('literal')
  }
}
function chargeObject(context: Budget, value: object, pending: object[]): void {
  const prototype: unknown = Object.getPrototypeOf(value)
  if (prototype === Array.prototype && Array.isArray(value)) {
    charge(context, 1 + value.length)
    for (const item of value) chargeItem(context, item, pending)
    return
  }
  if (prototype !== Object.prototype) fail('literal')
  const keys = Object.keys(value)
  charge(context, 1 + 2 * keys.length)
  for (const key of keys) {
    charge(context, stringWords(key.length))
    chargeItem(context, (value as Record<string, unknown>)[key], pending)
  }
}
// Each entry is two slots and its name's and value's payloads.
export function chargeParameters(context: DecodeContext, parameters: URLSearchParams): void {
  charge(context, 1)
  for (const entry of parameters)
    charge(context, 2 + stringWords(entry[0].length) + stringWords(entry[1].length))
}
