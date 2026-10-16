import { parseInputInvalid, stringifyValueUnsupported } from '../error'
export const maxArrayLength = 4_294_967_295
export function decodeFail(reason: string): never {
  throw parseInputInvalid(reason)
}
export function encodeFail(reason: string): never {
  throw stringifyValueUnsupported(reason)
}
export const int = (value: unknown, max = Number.MAX_SAFE_INTEGER): value is number =>
  typeof value === 'number' && Number.isSafeInteger(value) && value >= 0 && value <= max
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
