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

  constructor(domains: Domains, adapter: Adapter) {
    super()
    this.adapter = adapter
    this.best = undefined
    this.domains = domains
    this.failures = undefined
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
    // Opaque plan identity stays unique without an unbounded numeric counter.
    let state: Execution | undefined = startExecution({}, bindings)
    while (state?.phase === 'publishing') state = this.revise(state)
    return state?.phase === 'done' ? state : undefined
  }

  score(selection: Selection): number {
    let total = 0
    for (let node = 0; node < selection.length; node += 1)
      if (this.domains[node][selection[node]].retained) total += 1
    return total
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
    const state = this.attempt(selection)
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
  // if that plan is not accepted. The top tier's preference is the one it would have had
  // before any attempt, and the stream's first plan, already considered, is skipped.
  const head = headSelection(domains, distinctStorages)
  const first = head === undefined ? undefined : run.consider(head)
  if (first !== undefined) return first
  // The stream asks for the top tier's preference first, before its first plan.
  let ordinary = head !== undefined
  let skip = head !== undefined
  const preferFresh = (): ReadonlySet<number> => {
    if (!ordinary) return run.failures ?? NO_PREFERENCE
    ordinary = false
    return NO_PREFERENCE
  }
  for (const selection of selections(domains, preferFresh)) {
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
