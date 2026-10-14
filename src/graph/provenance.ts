import type { SpecialDecision, SpecialFacts } from '../types'

import { SPECIAL_REPLACEMENT } from '../constants'
/**
 * Chooses special-value identity from supplied provenance and native equivalence facts.
 *
 * @remarks
 * Registered copies restore only their explicit base. Other sources require agreement of
 * every current-backed, dependency and equivalence fact; storage selection is a later decision.
 */
export function chooseSpecial(facts: SpecialFacts): SpecialDecision {
  if (facts.origin === 'copy') return facts.equivalent ? 'base' : 'source'
  return facts.currentBacked && !facts.forced && facts.dependenciesStable && facts.equivalent
    ? 'source'
    : SPECIAL_REPLACEMENT[facts.origin]
}
