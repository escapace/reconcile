/** Compares backing-store bytes after the caller establishes the native observation boundary. */
export function bufferEquivalent(base: ArrayBufferLike, candidate: ArrayBufferLike): boolean {
  if (base.byteLength !== candidate.byteLength) return false
  const left = new Uint8Array(base)
  const right = new Uint8Array(candidate)
  for (let index = 0; index < left.length; index += 1)
    if (left[index] !== right[index]) return false
  return true
}
