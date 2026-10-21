/**
 * Classifies object-like values; functions are opaque atoms throughout the library.
 *
 * @internal
 */
export const isObject = (value: unknown): value is object =>
  typeof value === 'object' && value !== null

/**
 * Lists own keys with strings before symbols, as two native observations.
 *
 * @remarks
 * `Object.getOwnPropertyNames` keeps V8's fast own-key path; `Reflect.ownKeys` measured about
 * twice as slow on ordinary objects. Exotic `ownKeys` traps are normalized by this split.
 * @internal
 */
export function ownKeys(value: object): PropertyKey[] {
  const names: PropertyKey[] = Object.getOwnPropertyNames(value)
  const symbols = Object.getOwnPropertySymbols(value)
  if (symbols.length === 0) return names
  // Appended one by one: concat would read Symbol.isConcatSpreadable through the prototypes.
  for (let index = 0; index < symbols.length; index += 1) names.push(symbols[index])
  return names
}

/**
 * Finds the first own or inherited descriptor without invoking its getter.
 *
 * @param source - First object in the prototype chain, or `null` for an empty chain.
 * @param property - Property to resolve.
 * @returns The nearest descriptor, or `undefined` when the chain has no such property.
 * @internal
 */
export function propertyDescriptor(
  source: object | null,
  property: PropertyKey,
): PropertyDescriptor | undefined {
  let owner: object | null = source
  while (owner !== null) {
    const descriptor = Object.getOwnPropertyDescriptor(owner, property)
    if (descriptor !== undefined) return descriptor
    owner = Object.getPrototypeOf(owner) as object | null
  }
  return undefined
}

/**
 * Recognizes canonical array-index property names.
 *
 * @remarks
 * The string round trip excludes alternate numeric spellings such as `01`, `-0`, and `1e0`.
 * The upper bound excludes the array length sentinel, `2^32 - 1`.
 *
 * @param property - Property name before index classification; non-string keys are excluded.
 * @returns The index in `[0, 2^32 - 1)`, or `undefined` for an ordinary property name.
 * @internal
 */
export function arrayIndex(property: PropertyKey): number | undefined {
  if (typeof property !== 'string') return undefined
  // Every canonical index spelling starts with a digit; other names skip the numeric round trip.
  const first = property.charCodeAt(0)
  if (!(first >= 48) || !(first <= 57)) return undefined
  const index = (property as unknown as number) >>> 0
  return index !== 4_294_967_295 && String(index) === property ? index : undefined
}

/**
 * Checks property ownership without reading the value or trusting an object's own helpers.
 *
 * @internal
 */
export const hasOwn = (value: object, key: PropertyKey): boolean =>
  Object.prototype.hasOwnProperty.call(value, key)

/**
 * The own string keys of `value` that are not enumerable, or `undefined` when every one is.
 *
 * @remarks
 * One key listing decides the common case without reading a descriptor. The caller passes the
 * names it listed, and reads them again only through this listing.
 * @internal
 */
export function hiddenNames(value: object, names: readonly string[]): Set<PropertyKey> | undefined {
  if (Object.keys(value).length === names.length) return undefined
  const hidden = new Set<PropertyKey>()
  for (const key of names) if (!isEnumerable(value, key)) hidden.add(key)
  return hidden
}

/**
 * Checks whether an own property is enumerable without trusting an object's own helpers.
 *
 * @internal
 */
export const isEnumerable = (value: object, key: PropertyKey): boolean =>
  Object.prototype.propertyIsEnumerable.call(value, key)

/**
 * Whether an object is an atom: `instanceof` one of the listed constructors, read in one walk
 * of the prototype chain.
 *
 * @remarks
 * `Object.prototype`, `Array.prototype` and `null` end the walk, as their chains hold no listed
 * prototype. Types.Atoms.classify_atomic proves the walk decides `instanceof` for every listed
 * constructor, and classify_reads counts its `[[GetPrototypeOf]]` calls.
 *
 * @internal
 */
export function isAtomObject(value: object): boolean {
  const first = Object.getPrototypeOf(value) as object | null
  return (
    first !== Object.prototype &&
    first !== null &&
    first !== Array.prototype &&
    atomPrototype(first)
  )
}

/**
 * The walk after the first read, from an object's prototype: a caller that already read it
 * passes it on.
 *
 * @internal
 */
export function atomPrototype(first: object | null): boolean {
  for (
    let prototype = first;
    prototype !== null && prototype !== Object.prototype;
    prototype = Object.getPrototypeOf(prototype) as object | null
  )
    if (listedPrototype(prototype)) return true
  return false
}

/** Prototypes whose instances keep state in internal slots. */
const listedPrototype = (prototype: object): boolean =>
  prototype === RegExp.prototype ||
  prototype === Error.prototype ||
  prototype === WeakMap.prototype ||
  prototype === WeakSet.prototype ||
  prototype === Promise.prototype ||
  prototype === Number.prototype ||
  prototype === String.prototype ||
  prototype === Boolean.prototype ||
  prototype === BigInt.prototype ||
  prototype === Symbol.prototype ||
  (typeof WeakRef === 'function' && prototype === WeakRef.prototype) ||
  (typeof FinalizationRegistry === 'function' && prototype === FinalizationRegistry.prototype) ||
  (typeof Blob === 'function' && prototype === Blob.prototype)
