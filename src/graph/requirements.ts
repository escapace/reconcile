import { EMPTY_FACTS } from '../constants'
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
export class RequirementClosure<Fact = number> {
  declare readonly facts: Set<Fact>
  // Successor lists may repeat a consequence; admission already skips closed facts, so
  // the closure and its insertion order equal the deduplicated rule set.
  declare private readonly implications: Map<Fact, Fact[]>

  constructor() {
    this.facts = new Set()
    this.implications = new Map()
  }

  imply(antecedent: Fact, consequence: Fact): void {
    const successors = this.implications.get(antecedent)
    if (successors === undefined) this.implications.set(antecedent, [consequence])
    else successors.push(consequence)
    if (this.facts.has(antecedent)) this.require(consequence)
  }

  require(fact: Fact): void {
    propagate(this.facts, [fact], (next) => this.implications.get(next) ?? EMPTY_FACTS)
  }
}
