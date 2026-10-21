import { defineData } from './standard-prototypes'
/**
 * Creates one property of a new snapshot object as an own data property.
 *
 * @remarks
 * On `Object.prototype` or a null prototype, assignment of a key `Object.prototype` lacks
 * reaches nothing, so it creates the same data property as a definition; a key it holds, such as
 * `__proto__` or one any code added, is defined, as is every key on any other prototype, such as
 * a class's. An inherited setter therefore never runs, nothing inherited makes the write fail,
 * and the copy holds the value. A property copied from a non-enumerable one is defined
 * non-enumerable; writability and configurability are not copied. `PropertyWrite.constructFromOn`
 * is this decision.
 * @internal
 */
export function setOwnProperty(
  object: Record<PropertyKey, unknown>,
  key: PropertyKey,
  value: unknown,
  standard: boolean,
  enumerable = true,
): void {
  if (standard && enumerable && !(key in Object.prototype)) object[key] = value
  else defineData(object, key, value, enumerable)
}

/** Whether a new object's prototype is `Object.prototype` or null. */
export const standardPrototype = (prototype: object | null): boolean =>
  prototype === null || prototype === Object.prototype
