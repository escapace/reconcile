import type { Leaf } from './contracts'
// Correspondence: Refinement.lean leaf_contract / leaf_step_refines.
// These facets have no child yield. The caller reserves identity before invoking
// them; an error native extraction throws propagates.
import { encodeBytes } from './binary'
import { readDate, readBuffer, readParameters, readTemporal } from './native'

function captureDate(value: object) {
  const time = readDate(value)
  // As in Date.prototype.toJSON, an invalid time is null.
  return [Number.isNaN(time) ? null : time]
}

function captureBuffer(value: object) {
  return [encodeBytes(value as ArrayBuffer, readBuffer(value))]
}

function captureParameters(value: object) {
  return [readParameters(value)]
}

function captureTemporal(value: object, kind?: number) {
  const payload = readTemporal(value, kind!)
  // A Duration's ten fields, or the ISO text; the Temporal kind is the layout's key field.
  return typeof payload === 'string' ? [payload] : payload
}

// By the tag recognition gives; structural and dependent facets are frame state machines
// (frames.ts). Every tag has an own element, so no lookup reaches `Array.prototype`.
export const leafCaptures: ReadonlyArray<Leaf | undefined> = /* @__PURE__ */ Object.freeze([
  undefined,
  undefined,
  undefined,
  undefined,
  undefined,
  undefined,
  captureDate,
  captureBuffer,
  undefined,
  undefined,
  captureParameters,
  undefined,
  captureTemporal,
])
