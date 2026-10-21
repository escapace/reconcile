import { isObject } from './object-property'
import { isAtomObject } from './object-property'
import { publicationRejected } from './error'
import { capture } from './publication/capture'
import { publishGraph } from './publication/publication-engine'
import type { PublicationRegistry } from './types'
import { publicationTypes } from './types/builtins'

/**
 * Updates `current` in place to match `next`, keeping each existing object whose position in `next`
 * holds a value of the same type.
 *
 * @remarks
 * Values are matched by position: object properties by key, array elements by index, and `Map` and
 * `Set` entries by insertion order. A current object at a matched position is kept and updated when
 * the next value has the same type, such as object, array or `Map`; otherwise the position receives
 * the next value: a primitive or an object kept by reference, such as a function, `RegExp` or
 * `Error`, as it is, and any other object as a new copy.
 *
 * When `current` holds one object at two positions and `next` holds different objects there, the
 * object is kept at one of them, chosen deterministically, and the others receive new objects.
 * Afterwards `current` has the key order, array lengths and holes, entry order, shared references
 * and cycles of `next`.
 *
 * Dates, buffers and views at matched positions take the next value's time or bytes, and buffer
 * sharing follows `next`. A URL or `URLSearchParams` at a matched position takes the next value's
 * text, including parameter order and duplicate names, and a URL keeps its own `searchParams`
 * object. An equal Temporal value is kept, and a changed one at a nested position is replaced.
 * Arrays, `Map`, `Set`, dates, binary data, URLs and Temporal values carry only their elements,
 * entries, time, bytes or text: their other own properties, such as fields that a subclass
 * declares, are not updated on a kept object and are not copied to a new one.
 *
 * A changed own property is written by assignment, as application code writes it, so an own setter
 * runs and an own getter or setter is kept. An own getter or setter keeps its place in the key
 * order, and a getter without a setter must already hold its value. `reconcile` never writes or
 * overrides an inherited getter or setter, such as a class getter or setter. When `next` has an own
 * key that an object lacks, and assigning it would reach such a getter or setter, that object
 * cannot be updated in place: inside `current`, it is replaced by a new object; if it is `current`
 * itself, the call throws before any write. A `__proto__` key is always defined as an own data
 * property, so data never replaces a prototype. A property that `reconcile` adds is writable and
 * configurable and takes the enumerability of the property in `next`, so a non-enumerable one stays
 * hidden from key listing, spread and JSON; a property it keeps has its own attributes.
 *
 * `next` is read completely before `current` changes. When both arguments are objects, a successful
 * call returns `current`. When either is not an object, the call returns `next` and changes
 * nothing.
 *
 * An object in `next` that is already the object at the same property of the matched current object
 * stays in place: `reconcile` reads its contents once, as part of `next`, and does not change them
 * or read them again. `reconcile(state, { ...state, count: 1 })` therefore writes only `count`.
 * Objects inside it stay where they are unless `next` places them elsewhere, and the final state is
 * the same as if it had been updated. This does not apply to an object that refers to `current` or
 * `next` at any depth; such an object is updated like any other.
 *
 * Vue reactive proxies are supported. When `current` holds a proxy and its raw object at different
 * positions and `next` does not hold those same objects there, `reconcile` keeps at most one of
 * them and gives the other position a new object, because a write through one changes the other.
 *
 * @example
 * ```ts
 * const state = { user: { name: 'Ada' }, tags: ['a'] }
 * const result = reconcile(state, { user: { name: 'Grace' }, tags: ['a', 'b'] })
 * // result === state; state.user and state.tags are the same objects, updated in place
 * ```
 *
 * @param current - The value to update.
 * @param next - The value `current` should match. It is not modified.
 * @returns `current` when both arguments are objects, otherwise `next`.
 * @throws {@link ReconcileError} with type `PublicationRejected` when `current` cannot be made to
 * match `next`. Causes include `current` and `next` having different types, such as an object and
 * an array; `current` itself being a changed Temporal value, which is immutable and cannot be
 * updated in place; and `current` itself blocking a change by being non-extensible or by having a
 * read-only non-configurable property, a non-configurable property that `next` lacks, a getter
 * without a setter, a setter that does not store its value, an inherited getter or setter for a
 * key it lacks, or an own getter or setter that would have to move to reach the key order of
 * `next`. Inside `current`, such an object is replaced by a new one instead. At any depth, the
 * call also throws when a new object it creates would inherit, from its prototype, Vue's reactive
 * markers for the same raw object as another kept or new object. Writes made before the failure are
 * not rolled back.
 * @throws Errors thrown by getters, setters or proxy traps propagate unchanged, also without
 * rollback.
 */
export function reconcile<T>(current: unknown, next: T): T {
  return reconcileWith(publicationTypes, current, next)
}

export function reconcileWith<T>(types: PublicationRegistry, current: unknown, next: T): T {
  if (Object.is(current, next)) return current as T
  // An atom root, like a function, cannot be updated in place: the next value is the result.
  if (!isObject(current) || !isObject(next) || isAtomObject(next) || isAtomObject(current))
    return next
  const graph = capture(types, next, current)
  if (!publishGraph(types, graph, current)) throw publicationRejected()
  return current as T
}
