import type { EncodeContext, Leaf } from './contracts'
// Refinement.lean leaf_contract / leaf_step_refines checked before implementation.
// These facets have no child yield. The caller reserves identity before invoking
// them and retains parent IteratorClose behavior if native extraction throws.
import { encodeBytes } from './binary'
import { readDate, readBuffer, readParameters, readTemporal } from './native'

function captureDate(value: object) {
  const time = readDate(value)
  return [6, Number.isNaN(time) ? null : time]
}

function captureBuffer(value: object, context: EncodeContext) {
  const state = readBuffer(value)
  context.hasBuffers = true
  return [7, encodeBytes(state.buffer)]
}

function captureParameters(value: object) {
  return [10, readParameters(value)]
}

function captureTemporal(value: object, _context: EncodeContext, kind?: number) {
  const state = readTemporal(value, kind)
  return [11, state.kind, state.payload]
}

// Sparse by the existing wire tag; structural/dependent facets remain generators.
export const leafCaptures = /* @__PURE__ */ (() => {
  const leaves: Array<Leaf | undefined> = []
  leaves[6] = captureDate
  leaves[7] = captureBuffer
  leaves[10] = captureParameters
  leaves[11] = captureTemporal
  return Object.freeze(leaves)
})()
