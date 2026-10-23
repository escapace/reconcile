import { EMPTY_FACTS } from '../constants'
import { Detached } from '../standard-prototypes'
/**
 * Computes the least ordered closure of finite, native-compiled implication facts.
 *
 * @remarks
 * This performs no native reads. Semantic requirements and storage ownership must be compiled
 * separately; equal labels are meaningful only within the caller's fact domain.
 */
export function closeRequirements(
  seeds: readonly number[],
  implications: ReadonlyArray<readonly number[]>,
): ReadonlySet<number> {
  const closed = new Set<number>()
  propagate(closed, seeds, (fact) => implications[fact] ?? EMPTY_FACTS)
  return closed
}

/**
 * Admits each new fact once before expanding it, bounding the queue by unique facts.
 *
 * @remarks
 * The RequirementPropagation model proves the same expansion trace and completed insertion
 * order as lazy admission. Successors are private finite facts: no native observer can inspect
 * the temporarily advanced admission Set. Callers observe the closed Set only after return.
 */
function propagate<Fact>(
  closed: Set<Fact>,
  seeds: readonly Fact[],
  successors: (fact: Fact) => Iterable<Fact>,
): void {
  const pending: Fact[] = []
  admit(closed, pending, seeds)
  for (const fact of pending) admit(closed, pending, successors(fact))
}

function admit<Fact>(closed: Set<Fact>, pending: Fact[], facts: Iterable<Fact>): void {
  for (const fact of facts) {
    if (closed.has(fact)) continue
    closed.add(fact)
    pending.push(fact)
  }
}

/**
 * Maintains positive requirement closure as discovery supplies new implications.
 *
 * @remarks
 * An implication arriving after its antecedent is already known propagates before returning.
 * Both arrival orders derive the same closure; insertion order follows their supplied history.
 * No native observation or application callback runs during propagation.
 */
export class RequirementClosure<Fact = number> extends Detached {
  // The closed facts in insertion order; created on the first requirement or read.
  declare private known: Set<Fact> | undefined
  // Successor lists may repeat a consequence; admission already skips closed facts, so
  // the closure and its insertion order equal the deduplicated rule set. Created on the first
  // implication.
  declare private implications: Map<Fact, Fact[]> | undefined

  constructor() {
    super()
    this.known = undefined
    this.implications = undefined
  }

  /** The closed facts in insertion order: a live set that later requirements extend. */
  get facts(): Set<Fact> {
    return (this.known ??= new Set())
  }

  holds(fact: Fact): boolean {
    return this.known?.has(fact) === true
  }

  imply(antecedent: Fact, consequence: Fact): void {
    const implications = (this.implications ??= new Map<Fact, Fact[]>())
    const successors = implications.get(antecedent)
    if (successors === undefined) implications.set(antecedent, [consequence])
    else successors.push(consequence)
    if (this.holds(antecedent)) this.require(consequence)
  }

  // Admits the fact, then propagates from its successors. ClosureHistory's expandUnfolded_eq
  // proves this unfolding equal to propagating from the fact itself.
  require(fact: Fact): void {
    const facts = this.facts
    if (facts.has(fact)) return
    facts.add(fact)
    const implications = this.implications
    const successors = implications?.get(fact)
    if (successors !== undefined)
      propagate(facts, successors, (next) => implications!.get(next) ?? EMPTY_FACTS)
  }
}
