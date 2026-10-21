/**
 * Gives a copy its source's prototype when that differs from the kind's standard one, so a
 * subclass instance stays an instance of its subclass. CopyPrototype.adopt_eq proves skipping the
 * change for a standard prototype gives the same result.
 *
 * @internal
 */
export function adoptPrototype<T extends object>(
  target: T,
  prototype: object | null,
  standard: object,
): T {
  if (prototype !== standard) Object.setPrototypeOf(target, prototype)
  return target
}
