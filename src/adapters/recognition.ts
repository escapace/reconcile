import type { PrototypeRead, RecognitionRegistry } from '../types'
import { ATOM_KIND, OBJECT_KIND } from '../constants'
import { atomFrom, prototypeOf } from '../object-property'

/**
 * Unknown-identity ingress: the registry's kind, with the plain-object fallback split into
 * `ATOM_KIND` for objects the library keeps by reference (Types.Atoms.ingress). Known module IDs
 * bypass this boundary. A caller that shares `read` reads the prototype at most once with the
 * registry and keeps it for its later readers (Types.Ingress).
 */
export function recognize(
  types: Pick<RecognitionRegistry, 'recognize'>,
  value: object,
  read?: PrototypeRead,
): symbol {
  const kind = types.recognize(value, read)!
  return kind === OBJECT_KIND && atomFrom(prototypeOf(value, read)) ? ATOM_KIND : kind
}

/** Ingress without the atom split, for a caller that reads the prototype itself. */
export function recognizeStructure(
  types: Pick<RecognitionRegistry, 'recognize'>,
  value: object,
  read?: PrototypeRead,
): symbol {
  return types.recognize(value, read)!
}

/** Live validation of a known module ID; later unrelated predicates need not run. */
export function matchesKind(types: RecognitionRegistry, value: object, kind: symbol): boolean {
  return types.matches(kind, value)
}
