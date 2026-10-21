import { storageIdentity } from '../../adapters/vue'
import { isObject } from '../../object-property'
import type { DraftContext } from '../../types'

/**
 * The identity a draft compares when it decides membership: a draft counts as the object it
 * drafts and, in Vue reactive state, a Vue reactive proxy as its raw object; any other value is
 * itself (DraftMembers.includes_form).
 */
const memberIdentity = (context: DraftContext, value: unknown, vue: boolean): unknown => {
  if (!isObject(value)) return value
  const base = context.statesByIdentity.get(value)?.base ?? value
  return vue ? storageIdentity(base) : base
}

/** `ToIntegerOrInfinity`: `NaN` is 0; infinities stay; other numbers are truncated. */
const integerOrInfinity = (value: unknown): number => {
  const number = +(value as number)
  return Number.isNaN(number) ? 0 : Math.trunc(number)
}

/** `LengthOfArrayLike`: `length` read once and clamped to a valid array length. */
const lengthOf = (array: unknown[]): number =>
  Math.min(Math.max(integerOrInfinity(array.length), 0), Number.MAX_SAFE_INTEGER)

/** The first index a forward search visits, as `includes` and `indexOf` derive it. */
const start = (fromIndex: unknown, length: number): number => {
  const index = integerOrInfinity(fromIndex)
  return index >= 0 ? index : Math.max(length + index, 0)
}

/**
 * Builds the search methods of the array draft of `base`, keyed by the native methods they replace.
 *
 * @remarks
 * Each follows the native algorithm step by step: it reads `length` once, starts at `fromIndex`,
 * reads only the indices it visits and stops at the first match. It compares member identities,
 * so it finds an element whether the caller holds the object or its draft and, in Vue reactive
 * state, a Vue proxy of it (DraftMembers.includes_drafted, DraftMembers.indexOf_drafted,
 * DraftMembers.lastIndexOf_drafted).
 */
export function arraySearches(context: DraftContext, base: object): ReadonlyMap<unknown, unknown> {
  const vue = storageIdentity(base) !== base
  const identity = (value: unknown) => memberIdentity(context, value, vue)
  function includes(this: unknown, value: unknown, ...from: unknown[]) {
    const array = Object(this) as unknown[]
    const length = lengthOf(array)
    if (length === 0) return false
    const target = identity(value)
    for (let index = start(from[0], length); index < length; index += 1) {
      const element = identity(array[index])
      // SameValueZero: NaN finds NaN, and 0 finds -0.
      if (element === target || (Number.isNaN(element) && Number.isNaN(target))) return true
    }
    return false
  }
  function indexOf(this: unknown, value: unknown, ...from: unknown[]) {
    const array = Object(this) as unknown[]
    const length = lengthOf(array)
    if (length === 0) return -1
    const target = identity(value)
    for (let index = start(from[0], length); index < length; index += 1)
      if (index in array && identity(array[index]) === target) return index
    return -1
  }
  function lastIndexOf(this: unknown, value: unknown, ...from: unknown[]) {
    const array = Object(this) as unknown[]
    const length = lengthOf(array)
    if (length === 0) return -1
    const fromIndex = from.length === 0 ? length - 1 : integerOrInfinity(from[0])
    const target = identity(value)
    for (
      let index = fromIndex >= 0 ? Math.min(fromIndex, length - 1) : length + fromIndex;
      index >= 0;
      index -= 1
    )
      if (index in array && identity(array[index]) === target) return index
    return -1
  }
  return new Map<unknown, unknown>([
    [Array.prototype.includes, includes],
    [Array.prototype.indexOf, indexOf],
    [Array.prototype.lastIndexOf, lastIndexOf],
  ])
}
