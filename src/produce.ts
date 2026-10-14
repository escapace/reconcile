import { isObject } from './object-property'
import { DraftSession } from './draft-session'
import { Finalization } from './finalization'
import type { ImmutableRegistry } from './types'
import { produceTypes } from './types/builtins'

/**
 * Runs `recipe` on a writable draft of `current` and returns the next value, leaving `current`
 * unchanged.
 *
 * @remarks
 * The draft behaves like `current` but records changes instead of applying them. The recipe
 * returns the next value explicitly: the draft, a part of it, or any other value. Drafts inside
 * the returned value are turned back into ordinary values. If the recipe returns `current`
 * itself, its draft changes are discarded.
 *
 * The result reuses the parts of `current` the recipe left unchanged where it can, so it is not
 * detached from `current`; use `snapshot(produce(...))` for a detached copy. The result is not
 * frozen. An edit that is later undone restores the original object when its whole subtree ends
 * up equal, including key order, holes, shared references and cycles. A new object the recipe
 * creates stays distinct from an equal existing one.
 *
 * Plain objects, arrays, `Map` and `Set` become drafts when the recipe reads them. A `Set` draft
 * treats a draft and the object it drafts as the same member. Reading a `Date`, `ArrayBuffer`,
 * `DataView` or typed array gives the recipe a writable copy; an unchanged copy resolves back to
 * the original, and changed copies keep their buffer sharing. Other objects, such as class
 * instances, are drafted like plain objects: an unchanged one is kept, and a changed one is
 * rebuilt with the same prototype and own properties but without private fields or other
 * internal state. Primitives and functions are single values. Vue reactive wrappers that behave
 * like objects, arrays, maps or sets are supported.
 *
 * Reading a value or writing an equal value back does not count as a change. During the recipe,
 * getters run on every read and assignments call setters with the draft as `this`;
 * `Reflect.set` honors an explicit receiver. Reading descriptors or enumerating keys, for example
 * with `Object.keys`, returns draft values like ordinary reads, so it can create child drafts or
 * copies. Defining properties with `Object.defineProperty`, `Object.defineProperties` or
 * `Reflect.defineProperty` throws; use assignment instead.
 *
 * After the recipe returns, each getter in the result runs once, in depth-first order, with a
 * temporary draft as `this`. Its value becomes an ordinary data property, so an object with a
 * getter is always rebuilt. Writes the getter makes through `this` become part of the result;
 * changes it makes to other state are not isolated.
 *
 * Array drafts support normal iteration, including `for...of` and callback methods. Iterating a
 * draft `Map` or `Set` with `keys`, `values`, `entries`, `forEach` or `[Symbol.iterator]` throws.
 *
 * @example
 * ```ts
 * const current = { todos: [{ done: false }], filter: 'all' }
 * const next = produce(current, (draft) => {
 *   draft.todos[0].done = true
 *   return draft
 * })
 * // current is unchanged; next.todos is a new array; next.filter is still 'all'
 * ```
 *
 * @param current - The value to start from. It is not modified.
 * @param recipe - Receives a draft of `current` and returns the next value.
 * @typeParam T - Type of `current` and of the draft.
 * @typeParam R - Type of the value the recipe returns.
 * @returns The value the recipe returned, with drafts replaced by ordinary values. A recipe that
 * returns nothing yields `undefined`.
 * @throws {@link ReconcileError} while the recipe runs: `DraftIterationUnsupported` for draft
 * `Map` or `Set` iteration, `DraftDefinePropertyUnsupported` for reflective property definition,
 * `DraftArrayLengthRejected` or `DraftArrayIndexRejected` for an exotic array whose descriptors a
 * real array could not have, and `DraftWrapperIdentityChanged` or
 * `DraftWrapperIteratorMismatched` for a misbehaving reactive wrapper.
 * @throws {@link ReconcileError} after the recipe returns: `FinalizationAccessorUnstable` when a
 * getter adds a new getter to the result, and `FinalizationConstructionImpossible` when no
 * consistent result exists. `FinalizationStorageMissing` and `FinalizationChildInvalid` indicate
 * a bug in the library.
 * @throws Errors thrown by the recipe, getters, setters or proxy traps, and native `RangeError`s
 * for invalid array lengths, propagate unchanged.
 */
export function produce<T, R>(current: T, recipe: (draft: T) => R): R {
  return produceWith(produceTypes, current, recipe)
}

export function produceWith<T, R>(
  types: ImmutableRegistry,
  current: T,
  recipe: (draft: T) => R,
): R {
  const context = new DraftSession(types)
  const draft = context.createDraft(current)

  const result = recipe(draft)

  // If the recipe explicitly returns the original current value (same identity),
  // honor that intent and return it without finalization. This allows users to
  // "cancel" all draft mutations by returning the original.
  if ((result as unknown) === current) {
    return result
  }

  if (!isObject(result)) {
    return result
  }

  return new Finalization(context).run(result) as R
}
