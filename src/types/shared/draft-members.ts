import { isObject } from '../../object-property'
import type { DraftContext, DraftState } from '../../types'

/**
 * The first form of the object `drafted` drafts, other than `value`, that `holds` finds in
 * `container`: the object it was made from or its draft; `undefined` when `holds` finds none.
 */
export function draftedForm<C>(
  drafted: DraftState,
  value: unknown,
  container: C,
  holds: (container: C, form: unknown) => boolean,
): object | undefined {
  const { base, handle } = drafted
  if (base !== value && holds(container, base)) return base
  if (handle !== undefined && handle !== value && holds(container, handle)) return handle
  return undefined
}

/**
 * The original or the copy of `value` that `holds` finds in `container`: a read of a `Date`,
 * buffer, view or URL makes a copy, which counts as its original, as a draft does.
 */
export function copiedForm<C>(
  context: DraftContext,
  value: object,
  container: C,
  holds: (container: C, form: unknown) => boolean,
): object | undefined {
  const form = context.copyBase(value) ?? context.copyOf(value)
  return form !== undefined && holds(container, form) ? form : undefined
}

/**
 * The identity a draft compares when it decides membership, its key: the object a drafted value
 * drafts, whichever of its forms the draft was made from; the original
 * of the copy a read of a `Date`, buffer, view or URL makes; and any other value itself. Each read
 * therefore keeps its element's identity (DraftMembers.includesBy_drafted, includesBy_form).
 */
const memberIdentity = (context: DraftContext, value: unknown): unknown => {
  if (!isObject(value)) return value
  const drafted = context.statesByIdentity.get(value)
  if (drafted !== undefined) return drafted.base
  return context.copyBase(value) ?? value
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
const start = (from: readonly unknown[], length: number): number => {
  // An omitted `fromIndex` is not read, so no index `Array.prototype` holds stands in for it.
  const index = from.length === 0 ? 0 : integerOrInfinity(from[0])
  return index >= 0 ? index : Math.max(length + index, 0)
}

/**
 * Builds the search methods of an array draft, keyed by the native methods they replace.
 *
 * @remarks
 * Each follows the native algorithm step by step: it reads `length` once, starts at `fromIndex`,
 * reads only the indices it visits and stops at the first match. It compares member identities,
 * so it finds an element whether the caller holds the object or its draft
 * (DraftMembers.includesBy_drafted, indexOfBy_drafted, lastIndexOfBy_drafted). The searched
 * value's key is taken before the search drafts any element, and reading an element does not
 * change its key, so the search still finds an element the array holds.
 */
export function arraySearches(context: DraftContext): ReadonlyMap<unknown, unknown> {
  const held = (value: unknown) => memberIdentity(context, value)
  function includes(this: unknown, value: unknown, ...from: unknown[]) {
    const array = Object(this) as unknown[]
    const length = lengthOf(array)
    if (length === 0) return false
    const target = held(value)
    for (let index = start(from, length); index < length; index += 1) {
      const element = held(array[index])
      // SameValueZero: NaN finds NaN, and 0 finds -0.
      if (element === target || (Number.isNaN(element) && Number.isNaN(target))) return true
    }
    return false
  }
  function indexOf(this: unknown, value: unknown, ...from: unknown[]) {
    const array = Object(this) as unknown[]
    const length = lengthOf(array)
    if (length === 0) return -1
    const target = held(value)
    for (let index = start(from, length); index < length; index += 1) {
      if (!(index in array)) continue
      if (held(array[index]) === target) return index
    }
    return -1
  }
  function lastIndexOf(this: unknown, value: unknown, ...from: unknown[]) {
    const array = Object(this) as unknown[]
    const length = lengthOf(array)
    if (length === 0) return -1
    const fromIndex = from.length === 0 ? length - 1 : integerOrInfinity(from[0])
    const target = held(value)
    for (
      let index = fromIndex >= 0 ? Math.min(fromIndex, length - 1) : length + fromIndex;
      index >= 0;
      index -= 1
    ) {
      if (!(index in array)) continue
      if (held(array[index]) === target) return index
    }
    return -1
  }
  return new Map<unknown, unknown>([
    [Array.prototype.includes, includes],
    [Array.prototype.indexOf, indexOf],
    [Array.prototype.lastIndexOf, lastIndexOf],
  ])
}
