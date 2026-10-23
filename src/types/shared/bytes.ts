import { bufferByteLength } from './binary-native'

/** Compares backing-store bytes after the caller establishes the native observation boundary. */
export function bufferEquivalent(base: ArrayBufferLike, candidate: ArrayBufferLike): boolean {
  const length = bufferByteLength(base)
  if (length !== bufferByteLength(candidate)) return false
  const left = new Uint8Array(base)
  const right = new Uint8Array(candidate)
  for (let index = 0; index < length; index += 1) if (left[index] !== right[index]) return false
  return true
}
