import { addIncoming } from './incoming-consensus'
import type { Binding, Claims, Event, Execution, IncomingConsensus } from '../types'
import { CheckedNodes } from './checked'
import { claim, hasClaim, withClaim } from './claims'

/**
 * Folds construction labels into exact consensus, replacing per-node incoming lists.
 * The finite fold/guard correspondence is proved in `IncomingConsensus.lean`.
 */
export function startExecution(id: number | object, bindings: readonly Binding[]): Execution {
  const incoming: IncomingConsensus[] = []
  const claims: Claims[] = []
  for (let node = 0; node < bindings.length; node += 1) {
    incoming.push(undefined)
    claims.push(claim(bindings[node].mode))
  }
  for (const binding of bindings)
    for (const edge of binding.construction) {
      if (bindings[edge.node] === undefined) continue
      const previous = incoming[edge.node]
      incoming[edge.node] = addIncoming(previous, edge.identity)
    }
  return {
    bindings,
    claims,
    id,
    incoming,
    phase: 'publishing',
    revision: 0,
  }
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

// Rebinds a checked node to the exposed mode; any mismatch rejects the attempt.
function rebind(state: Execution, event: Extract<Event, { readonly tag: 'rebind' }>): Execution {
  if (state.phase !== 'checking') return state
  const binding = state.bindings[event.node]
  const incoming = state.incoming[event.node]
  if (
    binding === undefined ||
    binding.fixed ||
    binding.storage !== event.storage ||
    !binding.palette.includes(event.mode) ||
    hasClaim(state.claims[event.node], event.mode) ||
    (incoming !== undefined && incoming !== event.exposed)
  )
    return settled(state, 'rejected')
  const bindings = state.bindings.slice()
  bindings[event.node] = { ...binding, exposed: event.exposed, mode: event.mode }
  const claims = state.claims.slice()
  claims[event.node] = withClaim(claims[event.node], event.mode)
  return {
    bindings,
    claims,
    id: state.id,
    incoming: state.incoming,
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
