/**
 * Internal objects and native calls that do not depend on the state of `Object.prototype`.
 *
 * @remarks
 * A property added to `Object.prototype`, as data or as an accessor, under any name, must not
 * change what the library does with its own objects. Internal classes are detached from it,
 * internal records hold every field they read, and the descriptors the library passes to
 * `defineProperty` inherit nothing.
 * @internal
 */

/** Detaches a class's prototype from `Object.prototype`. */
function detached<C extends abstract new (...arguments_: never) => object>(constructor: C): C {
  Object.setPrototypeOf(constructor.prototype, null)
  return constructor
}

/**
 * The base of every internal class: its prototype inherits nothing.
 *
 * @remarks
 * Instances never read or write through `Object.prototype`: a field assigned in the constructor
 * is created as an own data property even if `Object.prototype` has a setter of that name, an
 * absent field reads as `undefined`, and a proxy handler gains no inherited traps. Each class
 * keeps its own prototype, so `instanceof` and its methods are unchanged, and the constant stays
 * pure, so an unused class is still removed from bundles.
 * @internal
 */
// eslint-disable-next-line typescript/no-extraneous-class -- the class carries only its prototype
export const Detached = /* @__PURE__ */ detached(class {})

/** A complete data descriptor, as a proxy trap or a definition reads it. */
export interface DataDescriptor {
  configurable: boolean
  enumerable: boolean
  value: unknown
  writable: boolean
}

/**
 * A new data descriptor that inherits nothing, for a caller that fills it and passes it to the
 * engine.
 * @internal
 */
export const dataDescriptor = (): DataDescriptor =>
  Object.setPrototypeOf(
    { configurable: true, enumerable: true, value: undefined, writable: true },
    null,
  ) as DataDescriptor

/**
 * A copy of an accessor descriptor with the given configurability, inheriting nothing. A
 * non-configurable result is also marked writable, as the draft's own descriptors are.
 * @internal
 */
export function accessorDescriptor(
  descriptor: PropertyDescriptor,
  configurable: boolean,
): PropertyDescriptor {
  const copy = Object.setPrototypeOf(
    {
      configurable,
      enumerable: descriptor.enumerable === true,
      // eslint-disable-next-line typescript/unbound-method -- the accessor is copied, not called
      get: descriptor.get,
      // eslint-disable-next-line typescript/unbound-method -- the accessor is copied, not called
      set: descriptor.set,
    },
    null,
  ) as PropertyDescriptor
  if (!configurable) copy.writable = true
  return copy
}

/**
 * Whether a property descriptor describes a data property. A descriptor that
 * `getOwnPropertyDescriptor` returns has an own `value` exactly when it does. `'value' in` alone
 * would also find one added to `Object.prototype`, so ownership is checked only then; `in` is
 * several times faster than `Object.hasOwn`.
 * @internal
 */
export const isDataDescriptor = (descriptor: PropertyDescriptor): boolean =>
  'value' in descriptor && (!('value' in Object.prototype) || Object.hasOwn(descriptor, 'value'))

/**
 * An array of `length` own `undefined` elements. Reading an element never reaches
 * `Array.prototype`, as reading a hole of `new Array(length)` would; with unmodified prototypes the
 * two read alike.
 * @internal
 */
export const denseArray = <T>(length: number): T[] => filledArray(length, undefined as T)

/**
 * An array of `length` own elements equal to `value`, as `new Array(length).fill(value)` makes it.
 * Assigning each element in a loop is faster than `fill` at every size.
 * @internal
 */
export function filledArray<T>(length: number, value: T): T[] {
  const array = new Array<T>(length)
  for (let index = 0; index < length; index += 1) array[index] = value
  return array
}

/**
 * An empty array detached from `Array.prototype`, for internal tables indexed sparsely: a missing
 * element reads as `undefined` whatever `Array.prototype` or `Object.prototype` holds.
 * @internal
 */
export const sparseArray = <T>(): T[] => Object.setPrototypeOf([], null) as T[]

// One complete data descriptor that inherits nothing, reused for every definition: the native
// operation reads all four fields before it calls a proxy trap or returns, so a nested call
// cannot change a definition in progress. The value is cleared after each use.
const data = /* @__PURE__ */ dataDescriptor()

/**
 * Defines an own data property with the given attributes, as `Reflect.defineProperty` does with
 * a complete data descriptor.
 * @internal
 */
export function defineData(
  target: object,
  key: PropertyKey,
  value: unknown,
  enumerable = true,
  configurable = true,
  writable = true,
): boolean {
  data.configurable = configurable
  data.enumerable = enumerable
  data.value = value
  data.writable = writable
  try {
    return Reflect.defineProperty(target, key, data)
  } finally {
    data.value = undefined
  }
}

const hidden = /* @__PURE__ */ (() =>
  Object.freeze(Object.setPrototypeOf({ enumerable: false }, null) as { enumerable: boolean }))()

/**
 * Makes an existing own property non-enumerable and leaves its other attributes unchanged.
 * @internal
 */
export const hide = (target: object, key: PropertyKey): boolean =>
  Reflect.defineProperty(target, key, hidden)

/**
 * Whether an array holds an element at `index`, asked as `index in array` asks it.
 *
 * @remarks
 * With unmodified standard prototypes `in` finds only the array's own element, and a proxy
 * observes it as `in`. An index that `Array.prototype` or `Object.prototype` holds would make a
 * hole read as present, so only then is the array asked for an own element.
 * @internal
 */
export const hasElement = (array: object, index: number): boolean =>
  index in array && (!(index in Array.prototype) || Object.hasOwn(array, index))

const objectLike = (value: unknown): value is object =>
  (typeof value === 'object' && value !== null) || typeof value === 'function'

/**
 * The built-in iterator methods of `Map` and `Set`, read as own properties when the module loads.
 * Called on an instance of its kind, each returns a fresh native iterator whose steps no other
 * code observes; any other call fails as the built-in fails. They are compared and applied, never
 * called as methods.
 * @internal
 */
export const nativeMapEntries: unknown = /* @__PURE__ */ (() =>
  Object.getOwnPropertyDescriptor(Map.prototype, 'entries')?.value as unknown)()
/** @internal */
export const nativeSetValues: unknown = /* @__PURE__ */ (() =>
  Object.getOwnPropertyDescriptor(Set.prototype, 'values')?.value as unknown)()

/**
 * A built-in getter, read when the module loads and called with an explicit receiver.
 * @internal
 */
export function builtinGetter(prototype: object, key: PropertyKey): (target: object) => unknown {
  // eslint-disable-next-line typescript/unbound-method -- Called with an explicit receiver.
  const get = Object.getOwnPropertyDescriptor(prototype, key)!.get!
  return (target) => Reflect.apply(get, target, []) as unknown
}

/** A built-in method of `Map` or `Set`, read when the module loads. */
const collectionMethod = (prototype: object, key: string) =>
  Object.getOwnPropertyDescriptor(prototype, key)!.value as (...parameters: unknown[]) => unknown
const mapSet = /* @__PURE__ */ collectionMethod(Map.prototype, 'set')
const mapDelete = /* @__PURE__ */ collectionMethod(Map.prototype, 'delete')
const setAdd = /* @__PURE__ */ collectionMethod(Set.prototype, 'add')
const setDelete = /* @__PURE__ */ collectionMethod(Set.prototype, 'delete')

/**
 * The built-in `set`, `add` and `delete` of `Map` and `Set`, called with an explicit receiver, so
 * a subclass's override or an own property of the receiver is not called. A copy that the library
 * builds is filled with them.
 * @internal
 */
export const builtinMapSet = (target: object, key: unknown, value: unknown): void => {
  Reflect.apply(mapSet, target, [key, value])
}
/** @internal */
export const builtinMapDelete = (target: object, key: unknown): void => {
  Reflect.apply(mapDelete, target, [key])
}
/** @internal */
export const builtinSetAdd = (target: object, value: unknown): void => {
  Reflect.apply(setAdd, target, [value])
}
/** @internal */
export const builtinSetDelete = (target: object, value: unknown): void => {
  Reflect.apply(setDelete, target, [value])
}

/** Marks the end of an iteration in {@link stepIterator}; no iterator can yield it. */
export const iterationDone: unique symbol = Symbol('iteration done')

/**
 * One step of an iterator, taken as `for...of` takes it: the result must be an object, its
 * `done` is read and, when it is falsy, its `value`.
 * @internal
 */
export function stepIterator(next: unknown, iterator: object): unknown {
  const result: unknown = Reflect.apply(next as () => unknown, iterator, [])
  if (!objectLike(result)) throw new TypeError('Iterator result is not an object')
  // eslint-disable-next-line typescript/strict-boolean-expressions -- `done` is read as ToBoolean
  if ((result as { done?: unknown }).done) return iterationDone
  return (result as { value?: unknown }).value
}

/**
 * The iterator `@@iterator` returns, obtained as `for...of` obtains it; a caller that has read
 * `@@iterator` already passes it.
 * @internal
 */
export function getIterator(
  iterable: unknown,
  method: unknown = (iterable as { [Symbol.iterator]?: unknown })[Symbol.iterator],
): object {
  const iterator: unknown = Reflect.apply(method as () => unknown, iterable, [])
  if (!objectLike(iterator))
    throw new TypeError('Result of the Symbol.iterator method is not an object')
  return iterator
}

// Whether a property is held by the object or a prototype before `Object.prototype`.
function heldBelowObjectPrototype(object: object, key: PropertyKey): boolean {
  for (let current: object | null = object; current !== null && current !== Object.prototype;)
    if (Object.hasOwn(current, key)) return true
    else current = Object.getPrototypeOf(current) as object | null
  return false
}

// The `return` method closing reaches. One that only `Object.prototype` holds, which an
// unmodified one never does, is not the iterator's: it is neither read nor called.
function returnMethod(iterator: object): unknown {
  if (Object.hasOwn(Object.prototype, 'return') && !heldBelowObjectPrototype(iterator, 'return'))
    return undefined
  const method = (iterator as { return?: unknown }).return
  return method === null ? undefined : method
}

/**
 * Closes an iterator that a loop leaves early, as `for...of` closes it.
 * @internal
 */
export function closeIterator(iterator: object): void {
  const method = returnMethod(iterator)
  if (method === undefined) return
  const result: unknown = Reflect.apply(method as () => unknown, iterator, [])
  if (!objectLike(result)) throw new TypeError('Iterator result is not an object')
}

/**
 * Closes an iterator that a loop leaves by a throw, as `for...of` closes it: the throw is the
 * outcome, whatever closing does.
 * @internal
 */
export function closeIteratorAfterThrow(iterator: object): void {
  try {
    const method = returnMethod(iterator)
    if (method !== undefined) Reflect.apply(method as () => unknown, iterator, [])
  } catch {
    // The throw that left the loop is the outcome.
  }
}

/**
 * `const [key, value] = entry`, with the iterator protocol of {@link stepIterator} and
 * {@link closeIterator}.
 * @internal
 */
export function entryPair(entry: unknown): readonly [unknown, unknown] {
  const iterator = getIterator(entry)
  const next = (iterator as { next?: unknown }).next
  const key = stepIterator(next, iterator)
  if (key === iterationDone) return [undefined, undefined]
  const value = stepIterator(next, iterator)
  if (value === iterationDone) return [key, undefined]
  closeIterator(iterator)
  return [key, value]
}

/**
 * The global `Temporal` namespace, read as an own property of `globalThis`, whose prototype chain
 * reaches `Object.prototype`.
 *
 * @remarks
 * Unless `Object.prototype` holds `Temporal`, the global read finds only the global's own
 * property, and it is much faster than asking for ownership.
 * @internal
 */
export const globalTemporal = (): unknown =>
  !('Temporal' in Object.prototype) || Object.hasOwn(globalThis, 'Temporal')
    ? (globalThis as { Temporal?: unknown }).Temporal
    : undefined
