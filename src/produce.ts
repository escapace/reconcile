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
 * The draft behaves like `current` but records changes instead of applying them. The recipe returns
 * the next value explicitly: the draft, a part of it or any other value. Drafts inside the returned
 * value are turned back into ordinary values. A draft that the result holds only in a prototype, a
 * closure, an object kept by reference such as a function or `Error`, a property that a built-in
 * value does not carry, or a Vue proxy such as `reactive(draft)` stays a draft. If the recipe
 * returns `current` itself, its draft changes are discarded. The recipe must be synchronous: a
 * returned `Promise` is kept as it is, and the draft it resolves to is never finished. Writes to a
 * draft after the recipe returns reach neither `current` nor the result.
 *
 * The result reuses the parts of `current` the recipe left unchanged where it can, so it is not
 * detached from `current`; use `snapshot(produce(...))` for a detached copy. `produce` does not
 * freeze the result. An edit that is later undone restores the original object when its whole
 * subtree ends up equal, including key order, holes, shared references and cycles. A new object the
 * recipe creates stays distinct from an equal existing one. A value the recipe assigns or returns
 * from outside `current` is kept as it is, unless the recipe changes it through the draft. When the
 * recipe assigns or returns an object from `current`, including `current` itself inside another
 * value, the result holds it with the changes made through its draft.
 *
 * Plain objects, arrays, `Map` and `Set` become drafts when the recipe reads them. Reading a
 * `Date`, `ArrayBuffer`, `DataView` or typed array gives the recipe a writable copy; if the recipe
 * does not change a copy, the result holds the original, and changed copies preserve their buffer
 * sharing. A changed copy is itself the result's value, so changing it after the recipe returns
 * changes the result. `URL` and `URLSearchParams` values are also copied when read; a URL's copy
 * and the copy of its `searchParams` stay linked, whichever the recipe reads first. A buffer and
 * its views, or a URL and its `searchParams`, are copied together only when the recipe changes one
 * of them. A native method that changes the query text, such as `sort` turning `%20` into `+`,
 * counts as a change even when the parameter entries stay equal. Temporal values are copied when
 * read; they are immutable, so assign the value returned by their methods. A Temporal value the
 * recipe reads but does not replace stays the original in the result.
 *
 * A changed array, `Map`, `Set`, `Date`, buffer, view, URL or `URLSearchParams` value keeps its
 * source's prototype, so an instance of a subclass stays one. Other objects, such as class
 * instances, are drafted like plain objects: an unchanged one is kept, and a changed one is rebuilt
 * with the same prototype and own properties but without private fields. A getter, setter or method
 * that uses a private field throws when it runs on the draft, which is not the instance that holds
 * the field. Primitives, including bigints, and objects kept by reference are not drafted; they are
 * read and assigned as they are, so a method that changes such a value, such as
 * `WeakMap.prototype.set`, changes the original. Objects kept by reference are functions, a
 * `RegExp`, `Error`, `Promise`, `WeakMap`, `WeakSet`, `WeakRef`, `FinalizationRegistry`, `Blob` or
 * `SharedArrayBuffer`, a boxed primitive and an instance of a subclass of one of them.
 *
 * Vue reactive proxies of objects, arrays, maps and sets are supported. Their drafts are not
 * reactive: `isReactive(draft)` is false, `toRaw(draft)` returns the draft, and array methods such
 * as `forEach` called on a draft receive drafts. A Vue proxy and its raw object are one object and
 * have one draft. When the recipe does not change the object, the result keeps the proxy and the
 * raw object where each was; when it does, the result holds one new object at each of their
 * positions.
 *
 * Reading a value or writing an equal value back does not count as a change. During the recipe,
 * getters run on every read and assignments call setters with the draft as `this`; `Reflect.set`
 * with an explicit receiver calls the setter with that receiver as `this`. Reflection, such as
 * `Object.getOwnPropertyDescriptor` or `Object.values`, returns the same draft values as ordinary
 * reads. Defining properties on an object or array draft with `Object.defineProperty`,
 * `Object.defineProperties` or `Reflect.defineProperty` throws `DraftDefinePropertyUnsupported`;
 * use assignment instead. `Object.freeze`, `Object.seal` and `Object.preventExtensions` throw a
 * `TypeError` on such a draft, as does `Object.setPrototypeOf` with a different prototype.
 *
 * Arrays, `Map`, `Set`, dates, binary data, URLs and Temporal values, including instances of their
 * subclasses, carry only their elements, entries, time, bytes or text. Their drafts and copies
 * refuse to set or delete any other property, such as a field that a subclass declares, as a
 * non-extensible object refuses a new one: in strict-mode code the assignment throws a `TypeError`.
 * An array draft still shows these properties; other drafts and copies do not, and a changed value
 * loses them in the result. A `Date`, buffer, view, URL or `URLSearchParams` value the recipe
 * changes stays non-extensible in the result.
 *
 * A draft follows its object's property attributes and extensibility: a read-only property refuses
 * writes, a non-configurable one refuses deletion and a non-extensible object, such as a sealed
 * one, refuses new properties, so a frozen object in `current` cannot be changed through its draft;
 * pass `snapshot(state)` to change frozen state. In the result, a changed object other than a
 * `Date`, buffer, view, URL or `URLSearchParams` value keeps its extensibility, a changed object
 * other than an array keeps the attributes of its existing data properties, and properties the
 * recipe adds are writable, enumerable and configurable. A frozen object other than an array,
 * without getters, that is rebuilt because a child changed is therefore frozen.
 *
 * After the recipe returns, each own getter in the result is called once, in depth-first order. An
 * object that the recipe did not change, and whose getters returned values the result keeps, stays
 * the original object with its getters; a getter that returns a draft, such as one returning
 * `this.items[0]`, makes its object new even when nothing changed. Otherwise the object is new, and
 * each getter is replaced by a data property that holds the value it returned and has the getter's
 * enumerability, or, in an array, is enumerable. Inside the getter, `this` is a draft of its
 * object: writes through `this` become part of the result, and changes to other objects take effect
 * immediately and are not undone.
 *
 * A `Map` or `Set` draft is an instance of its source's class: `instanceof`, `Symbol.toStringTag`
 * and `constructor` work as on the source. Its methods read the original until the first change and
 * then read and write a working copy of the same class, always with the built-in methods, so an
 * override on a subclass or on the instance never runs; a Vue reactive original is read through
 * Vue's methods. A method a subclass adds runs with the draft as `this`: it can call the draft's
 * methods, but the subclass's constructor never initializes the draft, so `super` calls to the
 * built-in methods and private fields throw on it, and fields the constructor sets are missing from
 * it. Array, `Map` and `Set` drafts
 * iterate like native collections,
 * including `for...of`, spreading and callback methods: object values come back as drafts, a write
 * during a walk shows up in it, and a walk that changes nothing keeps the original. `Map` keys are
 * not drafts: a walk gives the keys as the `Map` gives them, which in Vue reactive state is Vue's
 * proxy of the stored key. Changing a key object changes `current`. To change a key, delete its
 * entry and set a new one.
 *
 * Draft searches count an object and its draft as the same value: `includes`, `indexOf` and
 * `lastIndexOf` on an array draft, key lookup on a `Map` draft, and `has` and methods such as
 * `union` on a `Set` draft. A search for a Vue proxy also finds its raw object. In Vue reactive
 * state a search for a raw object also finds a Vue proxy of it; elsewhere it can miss one. `===` in
 * recipe code compares references, so compare such values with these methods or by a key.
 *
 * `Set` draft methods return this draft's members as drafts and an operand's values as the operand
 * gives them. An operand whose `has` is the built-in `Set` or `Map` method, or a Vue reactive `Set`
 * or `Map` of such an operand, finds a member whether it holds the object or its draft. Any other
 * operand's `has`, including a subclass override, receives drafts and must recognize them itself. A
 * draft has the `Set` methods that the runtime's `Set` has when this library is imported; install a
 * polyfill for them before importing it.
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
 * @param current - The value to start from. `produce` does not modify it; a recipe can, through
 * `Map` key objects and objects kept by reference.
 * @param recipe - Receives a draft of `current` and returns the next value.
 * @typeParam T - Type of `current` and of the draft.
 * @typeParam R - Type of the value the recipe returns.
 * @returns The value the recipe returned, with drafts replaced by ordinary values. A recipe that
 * returns nothing yields `undefined`.
 * @throws {@link ReconcileError} while the recipe runs: `DraftDefinePropertyUnsupported` for
 * reflective property definition on an object or array draft, `DraftArrayLengthRejected` or
 * `DraftArrayIndexRejected` for an array in `current`, such as a proxy, whose properties a real
 * array could not have, and `DraftWrapperIdentityChanged` or `DraftWrapperIteratorMismatched` for a
 * reactive proxy that reports inconsistent contents.
 * @throws {@link ReconcileError} after the recipe returns: `FinalizationAccessorUnstable` can be
 * thrown when a getter adds a getter to a part of the result that `produce` has already visited,
 * and `FinalizationConstructionImpossible` when no consistent result exists.
 * `FinalizationStorageMissing` and `FinalizationChildInvalid` indicate a bug in the library.
 * @throws Errors thrown by the recipe, getters, setters or proxy traps, and native errors, such as
 * a `RangeError` for an invalid array length or the engine's error for nesting that exceeds the
 * call stack, propagate unchanged.
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
