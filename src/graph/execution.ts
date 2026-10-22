import { addIncoming } from './incoming-consensus'
import type { Binding, Claims, Event, Execution, IncomingConsensus } from '../types'
import { CheckedNodes } from './checked'
import { claim, hasClaim, withClaim } from './claims'

/** Starts an attempt's plan; its claims and incoming consensus are derived at the first rebind. */
export function startExecution(id: number | object, bindings: readonly Binding[]): Execution {
  return {
    bindings,
    claims: undefined,
    id,
    incoming: undefined,
    phase: 'publishing',
    revision: 0,
  }
}

/** Each node's claim history before any rebind: the mode it was bound with. */
export function initialClaims(bindings: readonly Binding[]): Claims[] {
  const claims: Claims[] = []
  for (let node = 0; node < bindings.length; node += 1) claims.push(claim(bindings[node].mode))
  return claims
}

/**
 * Folds construction labels into exact consensus, replacing per-node incoming lists.
 * The finite fold/guard correspondence is proved in `IncomingConsensus.lean`.
 */
export function incomingConsensus(bindings: readonly Binding[]): IncomingConsensus[] {
  const incoming: IncomingConsensus[] = []
  for (let node = 0; node < bindings.length; node += 1) incoming.push(undefined)
  for (const binding of bindings)
    for (const edge of binding.construction) {
      if (bindings[edge.node] === undefined) continue
      const previous = incoming[edge.node]
      incoming[edge.node] = addIncoming(previous, edge.identity)
    }
  return incoming
}

// A state's plan with a terminal phase, written out field by field instead of spread.
function settled(state: Execution, phase: 'done' | 'rejected'): Execution {
  return {
    bindings: state.bindings,
    claims: state.claims,
    id: state.id,
    incoming: state.incoming,
    phase,
    revision: state.revision,
  }
}

/**
 * The state a publishing attempt reaches when its publication is acknowledged, every node's
 * readback matches and it finishes: done, with its plan unchanged. It equals advancing through
 * `published`, `checked` for each node and `finish` (Execution `check_all_done`), without the
 * checking state; the bindings are dense, as prepared.
 */
export function completeExecution(state: Execution): Execution {
  return state.phase === 'publishing' ? settled(state, 'done') : state
}

// Rebinds a checked node to the exposed mode; any mismatch rejects the attempt.
function rebind(state: Execution, event: Extract<Event, { readonly tag: 'rebind' }>): Execution {
  if (state.phase !== 'checking') return state
  // Only a rebind reads the summaries, and nothing before the first one changes them.
  const summary = state.incoming ?? incomingConsensus(state.bindings)
  const history = state.claims ?? initialClaims(state.bindings)
  const binding = state.bindings[event.node]
  const incoming = summary[event.node]
  if (
    binding === undefined ||
    binding.fixed ||
    binding.storage !== event.storage ||
    !binding.palette.includes(event.mode) ||
    hasClaim(history[event.node], event.mode) ||
    (incoming !== undefined && incoming !== event.exposed)
  )
    return settled(state, 'rejected')
  const bindings = state.bindings.slice()
  bindings[event.node] = { ...binding, exposed: event.exposed, mode: event.mode }
  const claims = history.slice()
  claims[event.node] = withClaim(claims[event.node], event.mode)
  return {
    bindings,
    claims,
    id: state.id,
    incoming: summary,
    phase: 'publishing',
    revision: state.revision + 1,
  }
}

/**
 * Applies a receipt-authenticated transition without changing the selected writer or storage.
 *
 * @remarks
 * Native payload checks occur outside this reducer. Checked membership is linearly owned by
 * the attempt: retain receipts rather than historical checking states. Every publication
 * revision gets a new empty store, while mode claims preserve earlier revision histories.
 */
export function advanceExecution(state: Execution, event: Event): Execution {
  if (
    event.id !== state.id ||
    event.revision !== state.revision ||
    state.phase === 'done' ||
    state.phase === 'rejected'
  )
    return state
  switch (event.tag) {
    case 'checked':
      if (state.phase === 'checking' && state.bindings[event.node] !== undefined)
        state.checked.add(event.node)
      return state
    case 'finish':
      return state.phase === 'checking' && state.checked.size === state.bindings.length
        ? settled(state, 'done')
        : state
    case 'published':
      return state.phase === 'publishing'
        ? {
            bindings: state.bindings,
            checked: new CheckedNodes(state.bindings.length),
            claims: state.claims,
            id: state.id,
            incoming: state.incoming,
            phase: 'checking',
            revision: state.revision,
          }
        : state
    case 'rebind':
      return rebind(state, event)
    case 'reject':
      return settled(state, 'rejected')
  }
}
