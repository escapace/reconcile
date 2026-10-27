import type { EncodeContext } from './contracts'
import { advances } from './frames'
import { frame, layout, node, slot } from './emit'
import { radixTrie } from './radix'
import { filledArray } from '../standard-prototypes'
// Correspondence: DFS.lean recursive_refines_stack / entries_unique, Inline.lean
// inline_matches_recursive, ShapeRadix.lean radix_eq_internAll and Positional.lean
// decode_encode_document / renumber_first_use.
export function encodeGraph(value: unknown): unknown[] {
  const context: EncodeContext = {
    bigints: undefined,
    boundaries: [],
    descriptors: [],
    ids: new Map(),
    layoutRoot: radixTrie(),
    layouts: [],
    payloads: [],
    plain: undefined,
    scalars: undefined,
    scratch: [],
    shapeRoot: radixTrie(),
    shapes: [],
    stack: [],
    top: 0,
  }
  const { descriptors, payloads, stack } = context
  const literal = enter(value, context)
  if (literal !== undefined) return literal
  // Each advance writes children in place and yields only after a child pushed its own frame, so
  // that subtree completes before the parent's next observation. A throw propagates as is.
  while (stack.length !== 0) {
    const current = stack[stack.length - 1]
    if (advances[current.tag]!(current, context)) {
      payloads[current.id] = current.row
      descriptors[current.id] = layout(current.tag, current.detail, current.runs, context)
      stack.pop()
    }
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
  const root = frame(-1, -1, undefined, value)
  root.row = []
  slot(root, value, context)
  if (!root.reference) return root.row
  return undefined
}
// Positional.lean renumber_first_use: interning the provisional ids in node order yields the
// first-use layout table; ShapeRadix.lean radix_renumber: the trie's ids meet its premise.
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
