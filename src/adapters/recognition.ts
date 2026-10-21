import type { RecognitionRegistry } from '../types'
import { ATOM_KIND, OBJECT_KIND } from '../constants'
import { isAtomObject } from '../object-property'

/**
 * Unknown-identity ingress: the registry's kind, with the plain-object fallback split into
 * `ATOM_KIND` for objects the library keeps by reference (Types.Atoms.ingress). Known module IDs
 * bypass this boundary.
 */
export function recognize(types: Pick<RecognitionRegistry, 'recognize'>, value: object): symbol {
  const kind = types.recognize(value)!
  return kind === OBJECT_KIND && isAtomObject(value) ? ATOM_KIND : kind
}

/** Ingress without the atom split, for a caller that reads the prototype itself. */
export function recognizeStructure(
  types: Pick<RecognitionRegistry, 'recognize'>,
  value: object,
): symbol {
  return types.recognize(value)!
}

/** Live validation of a known module ID; later unrelated predicates need not run. */
export function matchesKind(types: RecognitionRegistry, value: object, kind: symbol): boolean {
  return types.matches(kind, value)
}
