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

// The enumerability and writability `restoreAttributes` gives back, reused like `data`.
const attributes = /* @__PURE__ */ (() =>
  Object.setPrototypeOf({ enumerable: true, writable: true }, null) as {
    enumerable: boolean
    writable: boolean
  })()

/**
 * Gives an own data property the enumerability and writability it had, and leaves its value and
 * configurability as they are.
 * @internal
 */
export function restoreAttributes(
  target: object,
  key: PropertyKey,
  enumerable: boolean,
  writable: boolean,
): boolean {
  attributes.enumerable = enumerable
  attributes.writable = writable
  return Reflect.defineProperty(target, key, attributes)
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
 * The value of a built-in's own property, read when the module loads. A hardened runtime, such as
 * SES `lockdown()` or `node --frozen-intrinsics`, turns a method into an accessor whose getter
 * returns the method; that getter is called with `owner` as the receiver. Undefined when `owner`
 * lacks the property.
 * @internal
 */
export function builtinValue(owner: object, key: PropertyKey): unknown {
  const descriptor = Object.getOwnPropertyDescriptor(owner, key)
  if (descriptor === undefined) return undefined
  if (isDataDescriptor(descriptor)) return descriptor.value as unknown
  // eslint-disable-next-line typescript/unbound-method -- Called with an explicit receiver.
  const get = descriptor.get
  return get === undefined ? undefined : (Reflect.apply(get, owner, []) as unknown)
}

/**
 * The built-in iterator methods of `Map` and `Set`, read as own properties when the module loads.
 * Called on an instance of its kind, each returns a fresh native iterator whose steps no other
 * code observes; any other call fails as the built-in fails. They are applied, never called as
 * methods.
 */
const nativeMapEntries: unknown = /* @__PURE__ */ (() => builtinValue(Map.prototype, 'entries'))()
const nativeSetValues: unknown = /* @__PURE__ */ (() => builtinValue(Set.prototype, 'values'))()

const functionCall = /* @__PURE__ */ (() => builtinValue(Function.prototype, 'call'))() as (
  ...parameters: unknown[]
) => unknown
const functionBind = /* @__PURE__ */ (() => builtinValue(Function.prototype, 'bind'))() as (
  ...parameters: unknown[]
) => unknown

/**
 * `method` as a function that takes its receiver first: calling the result with `target` and
 * further arguments calls `method` with `target` as `this` and those arguments, as
 * `Reflect.apply` would, without building an argument list. Built with the built-in `call` and
 * `bind` read when the module loads; nothing it does is observable.
 * @internal
 */
export const uncurried = <Arguments extends unknown[], Result>(
  method: unknown,
): ((target: unknown, ...parameters: Arguments) => Result) =>
  Reflect.apply(functionBind, functionCall, [method]) as (
    target: unknown,
    ...parameters: Arguments
  ) => Result

/**
 * The first index of `value` in `array` by strict equality, or -1, through the built-in `indexOf`.
 * @internal
 */
export const indexIn = /* @__PURE__ */ (() =>
  uncurried<[value: unknown], number>(Array.prototype.indexOf))() as (
  array: readonly unknown[],
  value: unknown,
) => number

/**
 * A built-in getter, read when the module loads, as a function of its receiver.
 * @internal
 */
const builtinGetter = (prototype: object, key: PropertyKey): ((target: object) => unknown) =>
  // eslint-disable-next-line typescript/unbound-method -- Called with an explicit receiver.
  uncurried<[], unknown>(Object.getOwnPropertyDescriptor(prototype, key)!.get)

/** A built-in method of `Map`, `Set` or their iterators, read when the module loads. */
const collectionMethod = (prototype: object, key: PropertyKey) =>
  builtinValue(prototype, key) as (...parameters: unknown[]) => unknown

/**
 * The built-in operations on the contents of a `Map` or `Set`, read when the module loads and
 * called with an explicit receiver, so an override that a subclass, the instance or a patched
 * prototype holds is never called. Every function reads and writes collection contents with them.
 * @internal
 */
export const builtinMapGet = /* @__PURE__ */ (() =>
  uncurried<[key: unknown], unknown>(collectionMethod(Map.prototype, 'get')))() as (
  target: object,
  key: unknown,
) => unknown
/** @internal */
export const builtinMapHas = /* @__PURE__ */ (() =>
  uncurried<[key: unknown], boolean>(collectionMethod(Map.prototype, 'has')))() as (
  target: object,
  key: unknown,
) => boolean
/** @internal */
export const builtinMapSet = /* @__PURE__ */ (() =>
  uncurried<[key: unknown, value: unknown], unknown>(collectionMethod(Map.prototype, 'set')))() as (
  target: object,
  key: unknown,
  value: unknown,
) => unknown
/** @internal */
export const builtinMapDelete = /* @__PURE__ */ (() =>
  uncurried<[key: unknown], boolean>(collectionMethod(Map.prototype, 'delete')))() as (
  target: object,
  key: unknown,
) => boolean
/** @internal */
export const builtinMapClear = /* @__PURE__ */ (() =>
  uncurried<[], unknown>(collectionMethod(Map.prototype, 'clear')))() as (target: object) => unknown
/** @internal */
export const builtinSetHas = /* @__PURE__ */ (() =>
  uncurried<[value: unknown], boolean>(collectionMethod(Set.prototype, 'has')))() as (
  target: object,
  value: unknown,
) => boolean
/** @internal */
export const builtinSetAdd = /* @__PURE__ */ (() =>
  uncurried<[value: unknown], unknown>(collectionMethod(Set.prototype, 'add')))() as (
  target: object,
  value: unknown,
) => unknown
/** @internal */
export const builtinSetDelete = /* @__PURE__ */ (() =>
  uncurried<[value: unknown], boolean>(collectionMethod(Set.prototype, 'delete')))() as (
  target: object,
  value: unknown,
) => boolean
/** @internal */
export const builtinSetClear = /* @__PURE__ */ (() =>
  uncurried<[], unknown>(collectionMethod(Set.prototype, 'clear')))() as (target: object) => unknown
/** The built-in `size` getters of `Map` and `Set`. @internal */
export const builtinMapSize = /* @__PURE__ */ (() => builtinGetter(Map.prototype, 'size'))() as (
  target: object,
) => number
/** @internal */
export const builtinSetSize = /* @__PURE__ */ (() => builtinGetter(Set.prototype, 'size'))() as (
  target: object,
) => number

/** The built-in openers of `Map` and `Set` iterators and the built-in `next` of each. */
type Opener = (collection: object) => object
/** The built-in `next` of a native iterator, as a function of the iterator. */
export type Step = (iterator: object) => IteratorResult<unknown>
const opener = (prototype: object, key: string): Opener =>
  uncurried<[], object>(collectionMethod(prototype, key))
/**
 * Opens the built-in iterator of a `Map`'s entries or a `Set`'s members; the matching step
 * advances it.
 * @internal
 */
export const openMapEntries = /* @__PURE__ */ (() => uncurried<[], object>(nativeMapEntries))()
/** @internal */
export const openSetValues = /* @__PURE__ */ (() => uncurried<[], object>(nativeSetValues))()
/** @internal */
export const mapStep = /* @__PURE__ */ (() =>
  uncurried<[], IteratorResult<unknown>>(
    collectionMethod(Object.getPrototypeOf(new Map().entries()) as object, 'next'),
  ))() as Step
/** @internal */
export const setStep = /* @__PURE__ */ (() =>
  uncurried<[], IteratorResult<unknown>>(
    collectionMethod(Object.getPrototypeOf(new Set().values()) as object, 'next'),
  ))() as Step

const mapForEach = /* @__PURE__ */ (() =>
  uncurried<[each: (value: unknown, key: unknown) => void], undefined>(
    collectionMethod(Map.prototype, 'forEach'),
  ))()
const setForEach = /* @__PURE__ */ (() =>
  uncurried<[each: (member: unknown) => void], undefined>(
    collectionMethod(Set.prototype, 'forEach'),
  ))()

/**
 * Calls `each` with the value and key of every entry of a `Map`, in order, as the built-in
 * `forEach` calls it: a walk of the whole `Map` that makes no iterator.
 * @internal
 */
export const forEachBuiltinEntry = (
  map: object,
  each: (value: unknown, key: unknown) => void,
): void => {
  mapForEach(map, each)
}

/**
 * Calls `each` with every member of a `Set`, in order, with the built-in `forEach`.
 * @internal
 */
export const forEachBuiltinMember = (set: object, each: (member: unknown) => void): void => {
  setForEach(set, each)
}

/**
 * Calls `each` with the key and value of each entry of a `Map`, walked by the built-in iterator,
 * until `each` returns true; returns whether it did. The iterator is fresh and native: its steps
 * and `[key, value]` pairs are read by the built-ins, which nothing can observe, and it has no
 * `return` to close.
 * @internal
 */
export function eachBuiltinEntry(
  map: object,
  each: (key: unknown, value: unknown) => boolean,
): boolean {
  const iterator = openMapEntries(map)
  for (;;) {
    const step = mapStep(iterator) as IteratorResult<readonly [unknown, unknown]>
    if (step.done === true) return false
    if (each(step.value[0], step.value[1])) return true
  }
}

/**
 * Calls `each` with each member of a `Set`, walked by the built-in iterator, until `each` returns
 * true; returns whether it did.
 * @internal
 */
export function eachBuiltinMember(set: object, each: (member: unknown) => boolean): boolean {
  const iterator = openSetValues(set)
  for (;;) {
    const step = setStep(iterator)
    if (step.done === true) return false
    if (each(step.value)) return true
  }
}

const openMapKeys = /* @__PURE__ */ (() => opener(Map.prototype, 'keys'))()
const openMapValues = /* @__PURE__ */ (() => opener(Map.prototype, 'values'))()
const openSetEntries = /* @__PURE__ */ (() => opener(Set.prototype, 'entries'))()

/** A fresh native iterator over a `Map` or `Set` and the built-in `next` that steps it. */
export interface BuiltinIterator {
  readonly iterator: object
  readonly step: Step
}

/**
 * Opens the built-in `entries`, `keys` or `values` iterator of a `Map` (`map`) or a `Set`. A
 * `Set`'s keys are its values.
 * @internal
 */
export function openBuiltin(
  collection: object,
  map: boolean,
  walk: 'entries' | 'keys' | 'values',
): BuiltinIterator {
  const open = map
    ? walk === 'entries'
      ? openMapEntries
      : walk === 'keys'
        ? openMapKeys
        : openMapValues
    : walk === 'entries'
      ? openSetEntries
      : openSetValues
  return { iterator: open(collection), step: map ? mapStep : setStep }
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
