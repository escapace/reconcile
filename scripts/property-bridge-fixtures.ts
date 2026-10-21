import assert from 'node:assert/strict'
import { integerIn } from './lean-oracle'

/** A Lean key code: integer keys, names and symbols by residue, the label in the quotient. */
export function decodeKey(code: unknown, maximum: number, symbols: readonly symbol[]): PropertyKey {
  const value = integerIn(code, 0, maximum)
  const label = Math.floor(value / 3)
  const decoded = [String(label), `name-${label}`, symbols[label]][value % 3]
  assert.ok(decoded !== undefined)
  return decoded
}

/** A fixture prototype holding the named inherited descriptor for `key`. */
export function prototypeHolding<C>(
  descriptors: Partial<Record<string, (calls: C) => PropertyDescriptor | undefined>>,
  name: unknown,
  key: PropertyKey,
  calls: C,
): object {
  const make = descriptors[String(name)]
  assert.ok(make !== undefined, `Unknown inherited descriptor ${String(name)}`)
  const descriptor = make(calls)
  const prototype = {}
  if (descriptor !== undefined) Object.defineProperty(prototype, key, descriptor)
  return prototype
}
