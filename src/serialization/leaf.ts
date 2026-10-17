import type { EncodeContext, Leaf } from './contracts'
// Refinement.lean leaf_contract / leaf_step_refines checked before implementation.
// These facets have no child yield. The caller reserves identity before invoking
// them and retains parent IteratorClose behavior if native extraction throws.
import { encodeBytes, longBase64 } from './binary'
import { readDate, readBuffer, readParameters, readTemporal } from './native'

function captureDate(value: object) {
  const time = readDate(value)
  // As in Date.prototype.toJSON, an invalid time is null.
  return [Number.isNaN(time) ? null : time]
}

function captureBuffer(value: object, context: EncodeContext) {
  const state = readBuffer(value)
  const text = encodeBytes(state.buffer)
  if (text.length >= longBase64) context.hasBuffers = true
  return [text]
}

function captureParameters(value: object) {
  return [readParameters(value)]
}

function captureTemporal(value: object, _context: EncodeContext, kind?: number) {
  const payload = readTemporal(value, kind).payload
  // A Duration's ten fields, or the ISO text; the Temporal kind is the layout's key field.
  return typeof payload === 'string' ? [payload] : payload
}

// Sparse by node tag; structural/dependent facets remain generators.
export const leafCaptures = /* @__PURE__ */ (() => {
  const leaves: Array<Leaf | undefined> = []
  leaves[6] = captureDate
  leaves[7] = captureBuffer
  leaves[10] = captureParameters
  leaves[12] = captureTemporal
  return Object.freeze(leaves)
})()
