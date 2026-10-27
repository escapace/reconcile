/** The first value of `set` in iteration order. */
export const firstSetEntry = <T>(set: Set<T>): T => set.values().next().value!

/** The first entry of `map` in iteration order. */
export const firstMapEntry = <K, V>(map: Map<K, V>): readonly [K, V] => map.entries().next().value!

/** Every byte of `buffer`. */
export const bytesOf = (buffer: ArrayBufferLike): number[] => Array.from(new Uint8Array(buffer))

/** The bytes of the range that `view` covers in its buffer. */
export const bytesOfView = (view: ArrayBufferView): number[] =>
  Array.from(new Uint8Array(view.buffer, view.byteOffset, view.byteLength))
