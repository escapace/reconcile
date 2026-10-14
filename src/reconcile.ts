import { isObject } from './object-property'
import { publicationRejected } from './error'
import { capture } from './publication/capture'
import { publishGraph } from './publication/publication-engine'
import type { PublicationRegistry } from './types'
import { publicationTypes } from './types/builtins'

/**
 * Updates `current` in place to match `next` and returns `current`, keeping existing objects
 * wherever their position and kind allow.
 *
 * @remarks
 * Values are matched by position: plain-object properties by key, array elements by index, and
 * `Map` and `Set` entries by insertion order. A current object at a matched position is kept and
 * updated when its kind fits the next value; otherwise the next value takes its place. When two
 * positions compete for one object, a deterministic choice keeps it at one of them. Afterwards
 * `current` has the key order, array lengths and holes, entry order, shared references and
 * cycles of `next`. Dates, buffers and views at matched positions take the next value's time or
 * bytes, and buffer sharing follows `next`.
 *
 * `next` is read completely before `current` changes. When both arguments are objects, a
 * successful call returns `current`. When either is not an object, the call returns `next` and
 * changes nothing.
 *
 * An object in `next` that is already the object at the same property of the matched current
 * object is kept as it is. `reconcile(state, { ...state, count: 1 })` therefore reads the shared
 * children once and writes only the root. Nothing inside a kept object is changed or read back.
 * Other positions never take over an object from inside it, but an object that `next` itself
 * places elsewhere stays that object there. The result equals a full update. A kept object that
 * refers back to either root is updated normally instead.
 *
 * Vue reactive wrappers are supported. Two kept objects never end up sharing the raw storage
 * behind a wrapper.
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
 * @throws {@link ReconcileError} with type `PublicationRejected` when `current` cannot be made
 * to match `next`. Causes include roots of incompatible kinds, such as an object and an array; a
 * non-writable or non-configurable property, or a non-extensible object, that blocks a change;
 * two kept objects that would share storage; and a write that did not take effect. Writes made
 * before the failure are not rolled back.
 * @throws Errors thrown by getters, setters or proxy traps propagate unchanged, also without
 * rollback.
 */
export function reconcile<T>(current: unknown, next: T): T {
  return reconcileWith(publicationTypes, current, next)
}

export function reconcileWith<T>(types: PublicationRegistry, current: unknown, next: T): T {
  if (Object.is(current, next)) return current as T
  if (!isObject(current) || !isObject(next)) return next
  const graph = capture(types, next, current)
  if (!publishGraph(types, graph, current)) throw publicationRejected()
  return current as T
}
