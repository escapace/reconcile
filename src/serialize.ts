import { encodeGraph as encode } from './serialization/encode'
/**
 * Encodes a value as JSON data that {@link deserialize} restores, preserving shared references and
 * cycles.
 *
 * @remarks
 * Plain and null-prototype objects, arrays, `Map`, `Set`, `Date`, fixed-length `ArrayBuffer`, typed
 * arrays, `DataView`, `URL`, `URLSearchParams` and Temporal values are supported. `serialize`
 * rejects objects with other prototypes, such as a class instance, an instance of a subclass of
 * `Array` or a Node.js `Buffer`, because {@link deserialize} restores only standard prototypes. It
 * also rejects functions and symbols, and the symbol keys and non-enumerable properties of plain
 * and null-prototype objects. Pass `new Uint8Array(buffer)` for a `Buffer`; a view over
 * `buffer.buffer` can encode Node's whole allocation pool. Objects from another iframe or Node.js
 * `vm` context are rejected, plain objects and arrays included.
 *
 * `serialize` calls each getter once, in depth-first order, with the object being encoded as
 * `this`. An array, `Map` or `Set` is encoded from its elements or entries; its other own
 * properties, whatever their key or enumerability, are not encoded, and their getters are not
 * called. A `Map` or `Set` is read with the built-in methods, never an override on the instance. A
 * `Date`, buffer, view, `URL`, `URLSearchParams` or Temporal value is encoded from its
 * built-in value; its own and overriding properties are not read and are not encoded. Callers must
 * not modify standard built-ins or prototypes during the call, including inside getters.
 *
 * The result holds only arrays, strings, finite numbers, booleans and `null`, so `JSON.stringify`
 * writes it as text and `JSON.parse` reads it back. Only {@link deserialize} restores the value
 * from it. It carries no format version, so both sides must use the same version of this library.
 *
 * @example
 * ```ts
 * const node = { label: 'a', next: undefined as unknown, created: new Date(0) }
 * node.next = node
 * const text = JSON.stringify(serialize(node))
 * const copy = deserialize(JSON.parse(text), { maxBytes: 1_000_000 }) as typeof node
 * // copy.next === copy; copy.created is a Date
 * ```
 *
 * @param value - The value to encode.
 * @returns New JSON data representing the value.
 * @throws {@link ReconcileError} with type `SerializeValueUnsupported` for unsupported values.
 * @throws Errors from getters, iterators or native operations, unchanged.
 */
export function serialize(value: unknown): unknown {
  return encode(value)
}
