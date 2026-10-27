import assert from 'node:assert/strict'
import { integerIn } from './lean-oracle'
import { isReconcileError } from '../src/error'
import { reconcile } from '../src/reconcile'

/** A Lean key code: integer keys, names and symbols by residue, the label in the quotient. */
export function decodeKey(code: unknown, maximum: number, symbols: readonly symbol[]): PropertyKey {
  const value = integerIn(code, 0, maximum)
  const label = Math.floor(value / 3)
  const decoded = [String(label), `name-${label}`, symbols[label]][value % 3]
  assert.ok(decoded !== undefined)
  return decoded
}

const inheritedDescriptors: Partial<
  Record<string, (count: () => void) => PropertyDescriptor | undefined>
> = {
  accessor: (count) => ({ configurable: true, set: count, get: () => 7 }),
  data: () => ({ configurable: true, value: 7, writable: true }),
  getter: () => ({ configurable: true, get: () => 7 }),
  none: () => undefined,
  readonly: () => ({ configurable: true, value: 7, writable: false }),
}

/** A fresh inherited descriptor Lean names, whose setter, if any, calls `count`. */
export function inherited(name: unknown, count: () => void): PropertyDescriptor | undefined {
  const make = inheritedDescriptors[String(name)]
  assert.ok(make !== undefined, `Unknown inherited descriptor ${String(name)}`)
  return make(count)
}

/** A fixture prototype holding `descriptor`, if any, for `key`. */
export function prototypeHolding(
  descriptor: PropertyDescriptor | undefined,
  key: PropertyKey,
): object {
  const prototype = {}
  if (descriptor !== undefined) Object.defineProperty(prototype, key, descriptor)
  return prototype
}

/** Runs `run` while `Object.prototype` holds `descriptor`, if any, for `key`, which no other code
 * reads. */
export function holdingObjectPrototype<T>(
  descriptor: PropertyDescriptor | undefined,
  key: string,
  run: () => T,
): T {
  if (descriptor === undefined) return run()
  // eslint-disable-next-line no-extend-native -- the bridge installs a modified Object.prototype on purpose
  Object.defineProperty(Object.prototype, key, descriptor)
  try {
    return run()
  } finally {
    Reflect.deleteProperty(Object.prototype, key)
  }
}

/** Runs `reconcile` in place; false when it rejects the publication. */
export function reconciled(current: object, next: object): boolean {
  try {
    assert.equal(reconcile(current, next), current)
    return true
  } catch (error) {
    assert.ok(isReconcileError(error) && error.cause.type === 'PublicationRejected', String(error))
    return false
  }
}
