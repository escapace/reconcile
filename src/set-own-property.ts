import { hasOwn } from './object-property'

/**
 * Assigns a snapshot property while treating a missing `__proto__` as an own data key.
 *
 * @remarks
 * Other keys use ordinary assignment, including inherited and reactive setters. This snapshot
 * write policy intentionally differs from reconciliation's descriptor-aware publication and
 * from writes to a draft's private descriptor store.
 * @internal
 */
export function setOwnProperty(
  object: Record<PropertyKey, unknown>,
  key: PropertyKey,
  value: unknown,
): void {
  if (key === '__proto__' && !hasOwn(object, key)) {
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
