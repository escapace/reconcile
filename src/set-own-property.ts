// Publish an own __proto__ data key without invoking Object.prototype's setter.
// Other keys retain ordinary assignment behavior, including reactive setters.
export function setOwnProperty(
  object: Record<PropertyKey, unknown>,
  key: PropertyKey,
  value: unknown,
): void {
  if (key === '__proto__' && !Object.prototype.hasOwnProperty.call(object, key)) {
    Object.defineProperty(object, key, {
      configurable: true,
      enumerable: true,
      value,
      writable: true,
    })
  } else {
    object[key] = value
  }
}
