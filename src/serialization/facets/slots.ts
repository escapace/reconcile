import { decodeFail as fail, int, literal } from '../common'
import type { DecodeContext, Row } from '../contracts'
import { keyed } from '../layout'
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
// reference slots, literals first. References are replaced by their nodes in place, so fills
// read decoded values directly.
export function resolve(slots: Row, layout: number, context: DecodeContext): void {
  const { control, ends, output } = context
  const from = layout + (keyed(control[layout] as number) ? 2 : 1)
  const stop = layout + (control[layout - 1] as number)
  let cursor = context.cursor
  let position = 0
  for (let run = from; run <= stop; run++) {
    const end = runEnd(control, from, stop, run, position, slots.length)
    if ((run - from) % 2 === 0) literals(slots, position, end)
    else cursor = references(slots, position, end, output, ends, cursor)
    position = end
  }
  context.cursor = cursor
}
function literals(slots: Row, position: number, end: number): void {
  for (; position < end; position++) literal(slots[position])
}
// Preorder.lean check_iff: nodes are filled in reverse; a reference below the cursor names an
// entered node, one at the cursor enters it and moves the cursor to its subtree end, and one
// above the cursor is out of depth-first order. Returns the cursor.
function references(
  slots: Row,
  position: number,
  end: number,
  output: unknown[],
  ends: number[],
  cursor: number,
): number {
  for (; position < end; position++) {
    const id = slots[position]
    if (!int(id, output.length - 1)) fail('reference')
    if (id >= cursor) {
      if (id !== cursor) fail('node order')
      cursor = ends[id]
    }
    slots[position] = output[id]
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
