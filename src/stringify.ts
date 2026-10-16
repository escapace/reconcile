import { encodeGraph as encode } from './serialization/encode'
/**
 * Encodes a supported object graph as JSON text, preserving shared references and cycles.
 *
 * @remarks
 * Plain and null-prototype records, arrays, Map, Set, Date, fixed ArrayBuffer and views,
 * URL, URLSearchParams and available global Temporal value classes are supported.
 * Record getters run depth first with the source as receiver; symbol keys and unsupported
 * prototypes reject. Native values use native state and omit extra properties.
 * The wire contains no format identifier; communicating parties must use matching versions.
 * No size or allocation quotas are imposed. {@link parse} restores the graph; JSON.parse
 * alone returns the transport arrays.
 * @param value - The graph to encode.
 * @returns JSON text representing the graph.
 * @throws {@link ReconcileError} with type `StringifyValueUnsupported` for unsupported values.
 * @throws Errors from source observations or native operations, unchanged.
 */
export function stringify(value: unknown): string {
  return encode(value)
}
