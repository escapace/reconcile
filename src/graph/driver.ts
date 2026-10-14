import type { Adapter, Domains, Execution, Result, ScoredSelection, Selection } from '../types'
import { advanceExecution, startExecution } from './execution'
import { selections } from './selection'

/**
 * Executes ranked candidates until a completed native report certifies an acceptable image.
 *
 * @remarks
 * Each attempt owns its revision and claim domain. A provisional best result must be replayed
 * because later attempts may have overwritten native storage. Callbacks receive complete
 * bindings but cannot supply verification receipts. Native failure outcomes and propagated
 * user exceptions retain their separate public boundaries; no rollback is promised.
 */
export function execute(domains: Domains, adapter: Adapter): Result {
  const failures = new Set<number>()
  const failed = (node: number): void => {
    if (Number.isInteger(node) && node >= 0 && node < domains.length) failures.add(node)
  }
  // Publishes one revision and reads every node back; undefined when publication fails.
  const revise = (state: Execution): Execution | undefined => {
    const publication = adapter.publish(state)
    if (publication !== true) {
      if (publication !== false) failed(publication.rejected)
      return undefined
    }
    // Every event of one revision carries that revision's receipt.
    const id = state.id
    const revision = state.revision
    state = advanceExecution(state, { id, revision, tag: 'published' })
    for (let node = 0; node < domains.length; node += 1) {
      const result = adapter.readback(state, node)
      if (result.kind === 'match') {
        state = advanceExecution(state, { id, node, revision, tag: 'checked' })
        continue
      }
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
      if (state.phase === 'rejected') failed(result.node ?? node)
      break
    }
    return advanceExecution(state, { id, revision, tag: 'finish' })
  }
  const attempt = (selection: Selection): Execution | undefined => {
    const bindings = adapter.prepare(selection)
    if (bindings?.length !== domains.length) return undefined
    // Opaque plan identity stays unique without an unbounded numeric counter.
    let state: Execution | undefined = startExecution({}, bindings)
    while (state?.phase === 'publishing') state = revise(state)
    return state?.phase === 'done' ? state : undefined
  }
  const score = (selection: Selection): number => {
    let total = 0
    for (let node = 0; node < selection.length; node += 1)
      if (domains[node][selection[node]].retained) total += 1
    return total
  }
  let best: ScoredSelection | undefined
  // Replays the provisional best once a candidate bounded by `upper` cannot beat it. The best
  // is consumed either way.
  const settle = (upper: number): Execution | undefined => {
    const candidate = best
    if (candidate === undefined || upper > candidate.score) return undefined
    best = undefined
    const state = attempt(candidate.selection)
    if (state === undefined) return undefined
    const retained = adapter.retention?.(state) ?? score(candidate.selection)
    return Number.isInteger(retained) &&
      retained >= candidate.score &&
      retained <= score(candidate.selection)
      ? state
      : undefined
  }
  for (const selection of selections(domains, () => failures)) {
    const upper = score(selection)
    const settled = settle(upper)
    if (settled !== undefined) return { kind: 'accepted', state: settled }
    const state = attempt(selection)
    if (state === undefined) continue
    const observed = adapter.retention?.(state) ?? upper
    // A fresh allocation must not impersonate an old candidate. Native adapters
    // certify this bound; violating it rejects the supplied candidate facts.
    if (!Number.isInteger(observed) || observed < 0 || observed > upper) continue
    if (observed === upper) return { kind: 'accepted', state }
    if (best === undefined || observed > best.score) best = { score: observed, selection }
  }
  // Every retention score is at least 0, so the remaining best always replays.
  const state = settle(0)
  return state === undefined ? { kind: 'rejected' } : { kind: 'accepted', state }
}
