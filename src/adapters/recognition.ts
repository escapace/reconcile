import type { RecognitionRegistry } from '../types'

/** Unknown-identity ingress. Known module IDs bypass this boundary. */
export function recognize(types: RecognitionRegistry, value: object): symbol {
  return types.recognize(value)!
}

/** Live validation of a known module ID; later unrelated predicates need not run. */
export function matchesKind(types: RecognitionRegistry, value: object, kind: symbol): boolean {
  return types.matches(kind, value)
}
