import { decodeGraph as decode } from './serialization/parse'
/**
 * Restores an object graph from matching serialized JSON text.
 *
 * @remarks
 * References preserve shared identities and cycles. Collections use native insertion semantics:
 * repeated Map keys keep their first position and last value; repeated Set members keep their
 * first position. Every entry is decoded before insertion. Structural checks run before their
 * values are used; native parsing, constructors and allocation remain engine boundaries.
 * Standard built-ins and prototypes must remain unmodified throughout the call.
 * This transport is intended for trusted application state. Sparse array lengths use native
 * allocation, so short input can request substantial memory. The wire has no format identifier
 * or allocation quotas. The returned graph is mutable.
 * @param text - Text produced by a matching version of {@link stringify}.
 * @returns The reconstructed value.
 * @throws {@link ReconcileError} with type `ParseInputInvalid` for malformed wire structure.
 * @throws SyntaxError for invalid JSON, and native constructor or allocation errors unchanged.
 */
export function parse(text: string): unknown {
  return decode(text)
}
