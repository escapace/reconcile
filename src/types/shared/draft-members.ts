import { storageIdentity } from '../../adapters/vue'
import { isObject } from '../../object-property'
import type { DraftContext, DraftState } from '../../types'

/**
 * The first form of the object `drafted` drafts, other than `value`, that `holds` finds in
 * `container`: the object it was made from, its draft, or another view registered for it, such as
 * the raw object of a Vue proxy; `undefined` when `holds` finds none.
 */
export function draftedForm<C>(
  context: DraftContext,
  drafted: DraftState,
  value: unknown,
  container: C,
  flag: boolean,
  holds: (container: C, flag: boolean, form: unknown) => boolean,
): object | undefined {
  const { base, handle } = drafted
  if (base !== value && holds(container, flag, base)) return base
  if (handle !== undefined && handle !== value && holds(container, flag, handle)) return handle
  const views = context.viewsOf(drafted)
  for (let index = 0; index < views.length; index += 1)
    if (views[index] !== value && holds(container, flag, views[index])) return views[index]
  return undefined
}

/**
 * The form of `value`'s raw object that `holds` finds in `container`, when `value` is a Vue proxy:
 * the raw object itself or a form of its draft other than the one `drafted` already tried, or
 * `undefined` (DraftMembers.plainTargets).
 */
export function rawForm<C>(
  context: DraftContext,
  value: object,
  drafted: DraftState | undefined,
  container: C,
  flag: boolean,
  holds: (container: C, flag: boolean, form: unknown) => boolean,
): object | undefined {
  const storage = storageIdentity(value)
  if (storage === value) return undefined
  if (holds(container, flag, storage)) return storage
  const shared = context.statesByIdentity.get(storage)
  return shared === undefined || shared === drafted
    ? undefined
    : draftedForm(context, shared, storage, container, flag, holds)
}

/**
 * The identity a draft compares when it decides membership, its key: the storage of the draft of a
 * drafted value, which every view of that storage shares whichever view the draft was made from
 * (DraftMembers.drafted_key); the original of the copy a read of a `Date`, buffer, view or URL
 * makes; with `vue`, the raw object of a Vue proxy; and any other value itself. Each read
 * therefore keeps its element's identity (DraftMembers.includesBy_drafted, includesBy_form).
 */
const memberIdentity = (context: DraftContext, value: unknown, vue: boolean): unknown => {
  if (!isObject(value)) return value
  const drafted = context.statesByIdentity.get(value)
  if (drafted !== undefined) return storageIdentity(drafted.base)
  const base = context.copyBase(value) ?? value
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
const start = (from: readonly unknown[], length: number): number => {
  // An omitted `fromIndex` is not read, so no index `Array.prototype` holds stands in for it.
  const index = from.length === 0 ? 0 : integerOrInfinity(from[0])
  return index >= 0 ? index : Math.max(length + index, 0)
}

/**
 * Builds the search methods of the array draft of `base`, keyed by the native methods they replace.
 *
 * @remarks
 * Each follows the native algorithm step by step: it reads `length` once, starts at `fromIndex`,
 * reads only the indices it visits and stops at the first match. It compares member identities,
 * so it finds an element whether the caller holds the object or its draft
 * (DraftMembers.includesBy_drafted, indexOfBy_drafted, lastIndexOfBy_drafted). Outside Vue
 * reactive state it looks the searched value up by its key and by its key's raw object, so a
 * search for a Vue proxy finds its raw object and objects that share one draft find each other
 * (DraftMembers.plainTargets, plain_raw, plain_shared). The searched value's key is taken before
 * the search drafts any element, which changes an element's key at most from the value to its
 * storage, so the search still finds an element the array holds (plain_self_staged). In Vue
 * reactive state it compares raw objects (DraftMembers.includesBy_single).
 */
export function arraySearches(context: DraftContext, base: object): ReadonlyMap<unknown, unknown> {
  const vue = storageIdentity(base) !== base
  const held = (value: unknown) => memberIdentity(context, value, vue)
  // The raw object of the searched value's key, which `held` already gives in Vue reactive state.
  const raw = (target: unknown) => (vue || !isObject(target) ? target : storageIdentity(target))
  function includes(this: unknown, value: unknown, ...from: unknown[]) {
    const array = Object(this) as unknown[]
    const length = lengthOf(array)
    if (length === 0) return false
    const target = held(value)
    const other = raw(target)
    for (let index = start(from, length); index < length; index += 1) {
      const element = held(array[index])
      // SameValueZero: NaN finds NaN, and 0 finds -0.
      if (
        element === target ||
        element === other ||
        (Number.isNaN(element) && Number.isNaN(target))
      )
        return true
    }
    return false
  }
  function indexOf(this: unknown, value: unknown, ...from: unknown[]) {
    const array = Object(this) as unknown[]
    const length = lengthOf(array)
    if (length === 0) return -1
    const target = held(value)
    const other = raw(target)
    for (let index = start(from, length); index < length; index += 1) {
      if (!(index in array)) continue
      const element = held(array[index])
      if (element === target || element === other) return index
    }
    return -1
  }
  function lastIndexOf(this: unknown, value: unknown, ...from: unknown[]) {
    const array = Object(this) as unknown[]
    const length = lengthOf(array)
    if (length === 0) return -1
    const fromIndex = from.length === 0 ? length - 1 : integerOrInfinity(from[0])
    const target = held(value)
    const other = raw(target)
    for (
      let index = fromIndex >= 0 ? Math.min(fromIndex, length - 1) : length + fromIndex;
      index >= 0;
      index -= 1
    ) {
      if (!(index in array)) continue
      const element = held(array[index])
      if (element === target || element === other) return index
    }
    return -1
  }
  return new Map<unknown, unknown>([
    [Array.prototype.includes, includes],
    [Array.prototype.indexOf, indexOf],
    [Array.prototype.lastIndexOf, lastIndexOf],
  ])
}
