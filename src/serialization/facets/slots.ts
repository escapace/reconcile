import { decodeFail as fail, int, literal } from '../common'
import type { DecodeContext, Row } from '../contracts'
// Positional.lean kindsGo: the end of run `run` over `total` positions, for runs listed from
// `from`. Only the first run may be empty, no run may overrun the total, and the open last run
// is nonempty unless no run is listed.
export function runEnd(
  runs: unknown[],
  from: number,
  run: number,
  position: number,
  total: number,
): number {
  if (run === runs.length) {
    if (run !== from && position === total) fail('runs')
    return total
  }
  const size = runs[run]
  if (!int(size, total - position) || (size === 0 && run !== from)) fail('runs')
  return position + size
}
// Positional.lean decodeSlots: the layout's runs alternate literal and reference slots,
// literals first. References are replaced by their nodes in place, so fills read decoded
// values directly.
export function resolve(slots: Row, layout: number[], from: number, context: DecodeContext): void {
  let position = 0
  for (let run = from; run <= layout.length; run++) {
    const end = runEnd(layout, from, run, position, slots.length)
    if ((run - from) % 2 === 0) literals(slots, position, end)
    else references(slots, position, end, context)
    position = end
  }
}
function literals(slots: Row, position: number, end: number): void {
  for (; position < end; position++) literal(slots[position])
}
// Preorder.lean check_iff: nodes are filled in reverse; a reference below the cursor names an
// entered node, one at the cursor enters it and moves the cursor to its subtree end, and one
// above the cursor is out of depth-first order.
function references(slots: Row, position: number, end: number, context: DecodeContext): void {
  const { ends, output } = context
  let cursor = context.cursor
  for (; position < end; position++) {
    const id = slots[position]
    if (!int(id, output.length - 1)) fail('reference')
    if (id >= cursor) {
      if (id !== cursor) fail('node order')
      cursor = ends[id]
    }
    slots[position] = output[id]
  }
  context.cursor = cursor
}
// A view's buffer and a URL's own parameters are depth-first children outside slots.
export function enter(id: number, context: DecodeContext): void {
  if (id >= context.cursor) {
    if (id !== context.cursor) fail('node order')
    context.cursor = context.ends[id]
  }
}
