import type { IncomingConsensus, Label } from '../types'

/**
 * Adds an opaque identity to an exact universal-equality summary.
 *
 * @remarks
 * Undefined is empty, a number is a unanimous identity, and null is conflict.
 * IncomingConsensus.foldl_eq proves repeated updates agree with the finite list
 * reference. This combines captured labels and performs no native observations.
 */
export function addIncoming(previous: IncomingConsensus, identity: Label): IncomingConsensus {
  return previous === undefined || previous === identity ? identity : null
}
