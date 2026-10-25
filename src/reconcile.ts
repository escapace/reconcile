import { atomFrom, isObject } from './object-property'
import { publicationRejected } from './error'
import { capture } from './publication/capture'
import { publishGraph } from './publication/publication-engine'
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
 * `Error`, as it is, and any other object as a new copy. A kept object keeps its prototype: a class
 * instance updated from a plain object stays an instance of its class.
 *
 * When `current` holds one object at two positions and `next` holds different objects there, the
 * object is kept at the first of them in the order `reconcile` reads `next`, and the others
 * receive new objects. Afterwards `current` has the key order, array lengths and holes, entry
 * order, shared references and cycles of `next`.
 *
 * When `next` holds one object at two positions and `current` holds different objects there,
 * `reconcile` keeps the current object at the first of them in the order it reads `next`. It keeps
 * the current object at a later position instead when another object of `current` that
 * `reconcile` can keep holds that object in a read-only non-configurable property or a getter
 * without a setter, is a view over it or is the URL whose `searchParams` it is, so that the object
 * holding it can be kept too.
 *
 * Dates, buffers and views at matched positions take the next value's time or bytes, and buffer
 * sharing follows `next`. A URL or `URLSearchParams` at a matched position takes the next value's
 * text, including parameter order and duplicate names, and a URL keeps its own `searchParams`
 * object. An equal Temporal value is kept, and a changed one at a nested position is replaced. The
 * contents of a `Map`, `Set`, date, buffer, view, URL or `URLSearchParams` are read and written
 * with the built-in methods, so an override on a subclass or on the instance never runs. Arrays,
 * `Map`, `Set`, dates, binary data,
 * URLs and Temporal values carry only their elements, entries, time, bytes or text: their other own
 * properties, such as fields that a subclass declares, are not updated on a kept object and are not
 * copied to a new one.
 *
 * A changed own property is written by assignment, as application code writes it, so an own setter
 * runs and an own getter or setter is kept; a configurable read-only property is redefined with the
 * next value and keeps its attributes. An own getter or setter keeps its place in the key order,
 * and a getter without a setter must already hold its value. `reconcile` never writes or overrides
 * an inherited getter or setter, such as a class getter or setter. When `next` has an own key that
 * an object lacks, and assigning it would reach such a getter or setter, that object cannot be
 * updated in place: inside `current`, it is replaced by a new object; if it is `current` itself,
 * the call throws before any write. A `__proto__` key is always defined as an own data property, so
 * data never replaces a prototype. A property that `reconcile` adds, other than an array element, is
 * writable and configurable and takes the enumerability of the property in `next`, so a
 * non-enumerable one stays hidden from key listing, spread and JSON; a property it keeps has its
 * own attributes.
 *
 * On an object that `reconcile` keeps and updates, an own getter for a key that `next` also has
 * runs once when the call writes nothing and twice when it writes anything: once when `reconcile`
 * compares its value and again when it checks the result. When the check finds that an object
 * inside `current` blocked a change, for example through a setter that does not store its value,
 * `reconcile` replaces that object and tries again; each retry runs the getter at most once more.
 * These counts leave out reading `next`, which also runs the getters of any object of `current`
 * that `next` holds, and reads that a proxy trap makes.
 *
 * `next` is read completely before `current` changes. When both arguments are objects that are not
 * kept by reference, a successful call returns `current`. When either is a primitive, a function or
 * another object kept by reference, the call returns `next` and changes nothing.
 *
 * An object in `next` that is already the object at the same property or index of the matched
 * current object stays in place: `reconcile` reads its contents once, as part of `next`, and does
 * not change them or read them again. `reconcile(state, { ...state, count: 1 })` therefore writes
 * only `count`. Objects inside it stay where they are unless `next` places them elsewhere, and the
 * final state is the same as if it had been updated. This does not apply to an object that refers
 * to `current` or `next` at any depth, or to a key, value or member of a `Map` or `Set` that is not
 * itself in place, or anything inside one; such an object is updated like any other.
 *
 * @example
 * ```ts
 * const state = { user: { name: 'Ada' }, tags: ['a'] }
 * const result = reconcile(state, { user: { name: 'Grace' }, tags: ['a', 'b'] })
 * // result === state; state.user and state.tags are the same objects, updated in place
 * ```
 *
 * @param current - The value to update.
 * @param next - The value `current` should match. `reconcile` does not write to `next` itself, but
 * an object that `next` shares with `current` can change as part of `current`.
 * @returns `current` when both arguments are objects that are not kept by reference, otherwise
 * `next`.
 * @throws {@link ReconcileError} with type `PublicationRejected` when `current` cannot be made to
 * match `next`. Causes include `current` and `next` having different types, such as an object and
 * an array; `current` itself being a changed Temporal value, which is immutable and cannot be
 * updated in place; and `current` itself blocking a change to a property by being non-extensible or
 * by having a read-only non-configurable property, a non-configurable property that `next` lacks,
 * a getter without a setter, a setter that does not store its value, a proxy trap that refuses the
 * assignment, an inherited getter or setter for a key it lacks, an own getter or setter that would
 * have to move to reach the key order of `next`, or a value that another property's setter changes
 * during the call. Inside `current`, such an object is replaced by a new one instead. Writes made
 * before the failure are not rolled back.
 * @throws Errors thrown by getters, setters or proxy traps propagate unchanged, also without
 * rollback.
 */
export function reconcile<T>(current: unknown, next: T): T {
  if (Object.is(current, next)) return current as T
  // An atom root, like a function, cannot be updated in place: the next value is the result.
  if (!isObject(current) || !isObject(next)) return next
  // Capture reuses each root's prototype read here (Types.Ingress).
  const nextPrototype = Object.getPrototypeOf(next) as object | null
  if (atomFrom(nextPrototype)) return next
  const currentPrototype = Object.getPrototypeOf(current) as object | null
  if (atomFrom(currentPrototype)) return next
  const graph = capture(publicationTypes, next, current, nextPrototype, currentPrototype)
  if (!publishGraph(publicationTypes, graph, current)) throw publicationRejected()
  return current as T
}
