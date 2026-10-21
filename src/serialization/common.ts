import { deserializeInputInvalid, serializeValueUnsupported } from '../error'
import { defineData } from '../standard-prototypes'
export const maxArrayLength = 4_294_967_295
export function decodeFail(reason: string): never {
  throw deserializeInputInvalid(reason)
}
export function encodeFail(reason: string): never {
  throw serializeValueUnsupported(reason)
}
// A control integer; -0 is not one, so each control value has one JSON value.
export const int = (value: unknown, max = Number.MAX_SAFE_INTEGER): value is number =>
  typeof value === 'number' &&
  Number.isSafeInteger(value) &&
  value >= 0 &&
  value <= max &&
  (value !== 0 || 1 / value > 0)
/** Creates a record's property as own data: assignment where `Object.prototype` lacks the key,
 * so it reaches nothing, and a definition otherwise (`PropertyWrite.constructOn`). */
export function define(object: object, key: string, value: unknown): void {
  if (key in Object.prototype) defineData(object, key, value)
  else (object as Record<string, unknown>)[key] = value
}
