import type {
  Adapter,
  Domains,
  Execution,
  Readback,
  Result,
  ScoredSelection,
  Selection,
} from '../types'
import { Detached } from '../standard-prototypes'
import { advanceExecution, completeExecution, startExecution } from './execution'
import { headSelection, selections } from './selection'

// The top tier's preference before any attempt: no node prefers a fresh choice.
const NO_PREFERENCE: ReadonlySet<number> = /* @__PURE__ */ new Set()

// Per-call state of one `execute` run; its methods replace per-call closures.
class Run extends Detached {
  declare readonly adapter: Adapter
  declare best: ScoredSelection | undefined
  declare readonly domains: Domains
  // Nodes whose native publication or readback failed; created on the first failure.
  declare failures: Set<number> | undefined
  // Attempts made so far in this call; the next attempt's plan identity.
  declare plans: number

  constructor(domains: Domains, adapter: Adapter) {
    super()
    this.adapter = adapter
    this.best = undefined
    this.domains = domains
    this.failures = undefined
    this.plans = 0
  }

  failed(node: number): void {
    if (Number.isInteger(node) && node >= 0 && node < this.domains.length)
      (this.failures ??= new Set()).add(node)
  }

  // Publishes one revision and reads every node back; undefined when publication fails.
  revise(state: Execution): Execution | undefined {
    const adapter = this.adapter
    const publication = adapter.publish(state)
    if (publication !== true) {
      if (publication !== false) this.failed(publication.rejected)
      return undefined
    }
    // Readback ignores the phase, so every node is read back first; when all match, the
    // checking state's events are only replayed in effect (completeExecution).
    const size = this.domains.length
    let node = 0
    let result: Readback | undefined
    for (; node < size; node += 1) {
      result = adapter.readback(state, node)
      if (result.kind !== 'match') break
    }
    if (result === undefined || result.kind === 'match') return completeExecution(state)
    return this.mismatch(state, node, result)
  }

  // The rest of a revision whose readback of `node` did not match, after every earlier node did.
  mismatch(
    state: Execution,
    node: number,
    result: Exclude<Readback, { readonly kind: 'match' }>,
  ): Execution {
    // Every event of one revision carries that revision's receipt.
    const id = state.id
    const revision = state.revision
    state = advanceExecution(state, { id, revision, tag: 'published' })
    for (let checked = 0; checked < node; checked += 1)
      state = advanceExecution(state, { id, node: checked, revision, tag: 'checked' })
    state = advanceExecution(
      state,
      result.kind === 'reject'
        ? { id, revision, tag: 'reject' }
        : {
            exposed: result.exposed,
            id,
            mode: result.mode,
            node: result.node,
            revision,
            storage: result.storage,
            tag: 'rebind',
          },
    )
    if (state.phase === 'rejected') this.failed(result.node ?? node)
    return advanceExecution(state, { id, revision, tag: 'finish' })
  }

  attempt(selection: Selection): Execution | undefined {
    const bindings = this.adapter.prepare(selection)
    if (bindings?.length !== this.domains.length) return undefined
    // Each attempt of this call has its own number; plan 0 is a caller's head attempt.
    let state: Execution | undefined = startExecution((this.plans += 1), bindings)
    while (state?.phase === 'publishing') state = this.revise(state)
    return state?.phase === 'done' ? state : undefined
  }

  score(selection: Selection): number {
    return scoreOf(this.domains, selection)
  }

  // Replays the provisional best once a candidate bounded by `upper` cannot beat it. The best
  // is consumed either way.
  settle(upper: number): Execution | undefined {
    const candidate = this.best
    if (candidate === undefined || upper > candidate.score) return undefined
    this.best = undefined
    const state = this.attempt(candidate.selection)
    if (state === undefined) return undefined
    const retained = this.adapter.retention?.(state) ?? this.score(candidate.selection)
    return Number.isInteger(retained) &&
      retained >= candidate.score &&
      retained <= this.score(candidate.selection)
      ? state
      : undefined
  }

  // Attempts one streamed selection; a result ends the search.
  consider(selection: Selection): Result | undefined {
    const upper = this.score(selection)
    const settled = this.settle(upper)
    if (settled !== undefined) return { kind: 'accepted', state: settled }
    return this.conclude(selection, upper, this.attempt(selection))
  }

  // Judges a finished attempt of `selection` against its score bound, as consider does.
  conclude(selection: Selection, upper: number, state: Execution | undefined): Result | undefined {
    if (state === undefined) return undefined
    const observed = this.adapter.retention?.(state) ?? upper
    // A fresh allocation must not impersonate an old candidate. Native adapters
    // certify this bound; violating it rejects the supplied candidate facts.
    if (!Number.isInteger(observed) || observed < 0 || observed > upper) return undefined
    if (observed === upper) return { kind: 'accepted', state }
    if (this.best === undefined || observed > this.best.score)
      this.best = { score: observed, selection }
    return undefined
  }
}

// The number of retained choices a selection makes, as Run.score counts them.
export function scoreOf(domains: Domains, selection: Selection): number {
  let total = 0
  for (let node = 0; node < selection.length; node += 1)
    if (domains[node][selection[node]].retained) total += 1
  return total
}

/**
 * How the head plan's first revision ended when the caller ran it: not prepared, its
 * publication refused, a readback mismatch at `node` after every earlier node matched, or done.
 */
export type HeadOutcome =
  | {
      readonly node: number
      readonly result: Exclude<Readback, { readonly kind: 'match' }>
      readonly state: Execution
      readonly tag: 'mismatch'
    }
  | { readonly publication: false | { readonly rejected: number }; readonly tag: 'refused' }
  | { readonly state: Execution; readonly tag: 'done' }
  | { readonly tag: 'unprepared' }

/**
 * Executes ranked candidates until a completed native report certifies an acceptable image.
 *
 * @remarks
 * Each attempt owns its revision and claim domain. A provisional best result must be replayed
 * because later attempts may have overwritten native storage. Callbacks receive complete
 * bindings but cannot supply verification receipts. Native failure outcomes and propagated
 * user exceptions retain their separate public boundaries; no rollback is promised.
 */
export function execute(domains: Domains, adapter: Adapter, distinctStorages = false): Result {
  const run = new Run(domains, adapter)
  // The stream's first plan is often determined without searching; the search starts only
  // if that plan is not accepted.
  const head = headSelection(domains, distinctStorages)
  return search(run, head, head === undefined ? undefined : run.consider(head))
}

/**
 * Continues `execute` after the caller ran the head plan's first revision itself, as plan 0:
 * the driver finishes and judges that attempt exactly as Run.consider would, with the same
 * adapter calls in the same order, then searches on. Its own attempts are numbered from 1.
 */
export function continueExecution(
  domains: Domains,
  adapter: Adapter,
  head: Selection,
  outcome: HeadOutcome,
): Result {
  const run = new Run(domains, adapter)
  let state: Execution | undefined
  if (outcome.tag === 'refused') {
    if (outcome.publication !== false) run.failed(outcome.publication.rejected)
  } else if (outcome.tag === 'mismatch') {
    state = run.mismatch(outcome.state, outcome.node, outcome.result)
    while (state?.phase === 'publishing') state = run.revise(state)
    if (state?.phase !== 'done') state = undefined
  } else if (outcome.tag === 'done') state = outcome.state
  return search(run, head, run.conclude(head, scoreOf(domains, head), state))
}

// Searches the ranked stream after the head plan, considered with result `first`.
function search(run: Run, head: Selection | undefined, first: Result | undefined): Result {
  if (first !== undefined) return first
  // The top tier's preference is the one it would have had before any attempt, and the
  // stream's first plan, already considered, is skipped. The stream asks for the top tier's
  // preference first, before its first plan.
  let ordinary = head !== undefined
  let skip = head !== undefined
  const preferFresh = (): ReadonlySet<number> => {
    if (!ordinary) return run.failures ?? NO_PREFERENCE
    ordinary = false
    return NO_PREFERENCE
  }
  for (const selection of selections(run.domains, preferFresh)) {
    if (skip) {
      skip = false
      continue
    }
    const result = run.consider(selection)
    if (result !== undefined) return result
  }
  // Every retention score is at least 0, so the remaining best always replays.
  const state = run.settle(0)
  return state === undefined ? { kind: 'rejected' } : { kind: 'accepted', state }
}
