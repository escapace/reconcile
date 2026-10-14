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
  return symbols.length === 0 ? names : names.concat(symbols)
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
