import { parseInputInvalid, stringifyValueUnsupported } from '../error'
export const maxArrayLength = 4_294_967_295
export function decodeFail(reason: string): never {
  throw parseInputInvalid(reason)
}
export function encodeFail(reason: string): never {
  throw stringifyValueUnsupported(reason)
}
// A control integer; -0 is not one, so each control value has one JSON value.
export const int = (value: unknown, max = Number.MAX_SAFE_INTEGER): value is number =>
  typeof value === 'number' &&
  Number.isSafeInteger(value) &&
  value >= 0 &&
  value <= max &&
  (value !== 0 || 1 / value > 0)
export function define(object: object, key: string, value: unknown): void {
  if (key === '__proto__')
    Object.defineProperty(object, key, {
      configurable: true,
      enumerable: true,
      value,
      writable: true,
    })
  else (object as Record<string, unknown>)[key] = value
}
// A literal slot holds a JSON scalar that denotes itself; -0, nonfinite numbers and composites
// are not literals.
export function literal(value: unknown): unknown {
  if (
    typeof value === 'object'
      ? value !== null
      : typeof value === 'number' && (value - value !== 0 || (value === 0 && 1 / value < 0))
  )
    decodeFail('literal')
  return value
}
