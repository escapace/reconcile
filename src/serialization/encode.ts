import type { EncodeContext } from './contracts'
import { advances, closeFrame } from './frames'
import { frame, layout, node, slot } from './emit'
import { radixTrie } from './radix'
import { filledArray } from '../standard-prototypes'
// Correspondence: DFS.lean recursive_refines_stack / entries_unique, Inline.lean
// inline_matches_recursive, ShapeRadix.lean radix_matches_signature and Positional.lean
// decode_encode_document / renumber_first_use.
export function encodeGraph(value: unknown): unknown[] {
  const context: EncodeContext = {
    alias: -1,
    bigints: undefined,
    boundaries: [],
    descriptors: [],
    ids: new Map(),
    layoutRoot: radixTrie(),
    layouts: [],
    owners: undefined,
    payloads: [],
    plain: undefined,
    scalars: undefined,
    scans: undefined,
    scratch: [],
    shapeRoot: radixTrie(),
    shapes: [],
    stack: [],
    top: 0,
    views: undefined,
  }
  const { descriptors, payloads, stack } = context
  const literal = enter(value, context)
  if (literal !== undefined) return literal
  try {
    // Each advance writes children in place and yields only after a child pushed its own
    // frame, so that subtree completes before the parent's next observation.
    while (stack.length !== 0) {
      const current = stack[stack.length - 1]
      if (advances[current.tag](current, context)) {
        payloads[current.id] = current.row
        descriptors[current.id] = layout(current.tag, current.detail, current.runs, context)
        stack.pop()
      }
    }
  } catch (error) {
    // Native IteratorClose on an abrupt throw preserves the original completion.
    for (let index = stack.length - 1; index >= 0; index--) {
      try {
        closeFrame(stack[index])
      } catch {}
    }
    throw error
  }
  if (context.owners !== undefined)
    for (const entry of context.owners) {
      const parameters = entry[0]
      const owner = entry[1]
      payloads[parameters] = [owner]
      descriptors[parameters] = layout(11, undefined, -1, context)
    }
  return document(context)
}
// The root is one slot: a literal document, or node 0 with the control table and payloads.
function document(context: EncodeContext): unknown[] {
  const layouts = renumber(context)
  return [controlTable(context, layouts), context.payloads]
}
function enter(value: unknown, context: EncodeContext): unknown[] | undefined {
  if (value !== null && typeof value === 'object') {
    node(value, context)
    return undefined
  }
  const root = frame(-1, -1, undefined, value, false)
  root.row = []
  slot(root, value, context)
  if (!root.reference) return root.row
  context.top = 0
  return undefined
}
// Positional.lean renumber_first_use: interning the provisional ids in node order yields the
// first-use layout table.
function renumber(context: EncodeContext): number[][] {
  const { descriptors, layouts: provisional } = context
  const order = filledArray(provisional.length, -1)
  const layouts: number[][] = []
  for (let index = 0; index < descriptors.length; index++) {
    const id = descriptors[index]
    let next = order[id]
    if (next < 0) {
      next = order[id] = layouts.length
      layouts.push(provisional[id])
    }
    descriptors[index] = next
  }
  return layouts
}
// Positional.lean encodeControl: each node's layout id, the number of shapes, each shape framed
// by its length, then each layout framed by its length.
function controlTable(context: EncodeContext, layouts: number[][]): unknown[] {
  // The layout ids open the table, so it extends the descriptor array in place.
  const control: unknown[] = context.descriptors
  control.push(context.shapes.length)
  for (const table of [context.shapes, layouts] as unknown[][][])
    for (const entry of table) {
      control.push(entry.length)
      for (const item of entry) control.push(item)
    }
  return control
}
