import { nativeKind } from '../native'
import { encodeFail as fail } from '../common'
export function recognize(value: object): { tag: number; detail?: number } {
  const prototype = Object.getPrototypeOf(value) as object | null
  if (Array.isArray(value)) return { tag: 2 }
  if (prototype === Object.prototype) return { tag: 0 }
  if (prototype === null) return { tag: 1 }
  if (prototype === Map.prototype) return { tag: 4 }
  if (prototype === Set.prototype) return { tag: 5 }
  return nativeKind(value, prototype) ?? fail('unsupported prototype')
}
