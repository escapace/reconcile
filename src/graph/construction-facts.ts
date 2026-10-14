import type { CapturedNode, NativeRegistry, ConstructionPolicy } from '../types'

import { EMPTY_FACTS } from '../constants'

/** Reads only sealed module facts; native construction readback remains separate. */
export function constructionDependencies(
  types: NativeRegistry<ConstructionPolicy>,
  node?: CapturedNode,
): readonly number[] {
  if (node === undefined) return EMPTY_FACTS
  const bindings = types.policies[node.layout.kind].bindings
  return bindings.tag === 'dependent' ? bindings.dependencies(node) : EMPTY_FACTS
}
