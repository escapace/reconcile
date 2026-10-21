import { decodeFail as fail, int } from '../common'
import type { DecodeContext, Row } from '../contracts'
import { keyed } from '../layout'
import { charge, chargeLiteral, stringWords } from '../size'
// Positional.lean kindsGo: the end of the run at index `run` over `total` positions, for runs
// listed in runs[from ..< stop). Only the first run may be empty, no run may overrun the total,
// and the open last run is nonempty unless no run is listed.
export function runEnd(
  runs: unknown[],
  from: number,
  stop: number,
  run: number,
  position: number,
  total: number,
): number {
  if (run === stop) {
    if (run !== from && position === total) fail('runs')
    return total
  }
  const size = runs[run]
  if (!int(size, total - position) || (size === 0 && run !== from)) fail('runs')
  return position + size
}
// Positional.lean decodeSlots: the runs of the layout at `layout` alternate literal and
// reference slots, literals first. A literal is any JSON value, as JSON.parse produced it, so
// with no size limit only references are read: each is replaced by its node in place, and fills
// read decoded values directly. Under a limit, every literal and every bigint occurrence is
// charged where it occurs. Measuring checks and charges the same slots but replaces none.
export function resolve(slots: Row, layout: number, context: DecodeContext): void {
  const { control, ends, limited, measuring, output, weights } = context
  const from = layout + (keyed(control[layout] as number) ? 2 : 1)
  const stop = layout + (control[layout - 1] as number)
  let cursor = context.cursor
  let position = 0
  for (let run = from; run <= stop; run++) {
    const end = runEnd(control, from, stop, run, position, slots.length)
    if ((run - from) % 2 === 1) {
      if (weights !== undefined) charge(context, occurrences(slots, position, end, weights))
      cursor = references(slots, position, end, output, ends, cursor, measuring)
    } else if (limited) charge(context, literalWords(context, slots, position, end))
    position = end
  }
  context.cursor = cursor
}
// The words of a run of literals. A string is measured here; anything else that is not a number,
// boolean or null, such as a JSON object or array, which the encoder never writes, is checked
// and charged by `chargeLiteral`.
function literalWords(context: DecodeContext, slots: Row, position: number, end: number): number {
  let words = 0
  for (; position < end; position++) {
    const literal = slots[position]
    if (typeof literal === 'string') words += stringWords(literal.length)
    else if (literal !== null && typeof literal !== 'number' && typeof literal !== 'boolean')
      chargeLiteral(context, literal)
  }
  return words
}
// The words of the bigints these references name, read before they are replaced; only
// documents with a bigint under a limit have weights. A reference out of range reads no weight,
// and `references` then rejects it.
function occurrences(slots: Row, position: number, end: number, weights: number[]): number {
  let words = 0
  for (; position < end; position++) {
    const id = slots[position]
    if (int(id, weights.length - 1)) words += weights[id]
  }
  return words
}
// Preorder.lean check_iff: nodes are filled in reverse; a reference below the cursor names an
// entered node, one at the cursor enters it and moves the cursor to its subtree end, and one
// above the cursor is out of depth-first order. Returns the cursor. Measuring leaves the
// reference in place.
function references(
  slots: Row,
  position: number,
  end: number,
  output: unknown[],
  ends: number[],
  cursor: number,
  measuring: boolean,
): number {
  for (; position < end; position++) {
    const id = slots[position]
    if (!int(id, output.length - 1)) fail('reference')
    if (id >= cursor) {
      if (id !== cursor) fail('node order')
      cursor = ends[id]
    }
    if (!measuring) slots[position] = output[id]
  }
  return cursor
}
// A view's buffer and a URL's own parameters are depth-first children outside slots.
export function enter(id: number, context: DecodeContext): void {
  if (id >= context.cursor) {
    if (id !== context.cursor) fail('node order')
    context.cursor = context.ends[id]
  }
}
