import type { SpecialDecision, SpecialFacts } from '../types'

import { SPECIAL_REPLACEMENT } from '../constants'
/**
 * Chooses special-value identity from supplied provenance and native equivalence facts.
 *
 * @remarks
 * Registered copies restore only their explicit base. Other sources, from `current` or from
 * outside it, stay themselves when no linked owner forces a clone and their dependencies and
 * copy agree; storage selection is a later decision. The origin of the slot does not decide it.
 */
export function chooseSpecial(facts: SpecialFacts): SpecialDecision {
  if (facts.origin === 'copy') return facts.equivalent ? 'base' : 'source'
  return !facts.forced && facts.dependenciesStable && facts.equivalent
    ? 'source'
    : SPECIAL_REPLACEMENT[facts.origin]
}
