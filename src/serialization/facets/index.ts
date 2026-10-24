import { nativeKind } from '../native'
import { encodeFail as fail } from '../common'
export function recognize(
  value: object,
  prototype: object | null,
): { detail: number | undefined; tag: number } {
  // deserialize builds standard arrays, so an array with another prototype is rejected.
  if (Array.isArray(value))
    return prototype === Array.prototype
      ? { detail: undefined, tag: 2 }
      : fail('unsupported prototype')
  if (prototype === Object.prototype) return { detail: undefined, tag: 0 }
  if (prototype === null) return { detail: undefined, tag: 1 }
  if (prototype === Map.prototype) return { detail: undefined, tag: 4 }
  if (prototype === Set.prototype) return { detail: undefined, tag: 5 }
  return nativeKind(value, prototype) ?? fail('unsupported prototype')
}
