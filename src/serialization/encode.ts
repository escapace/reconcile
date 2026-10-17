import type { Row, EncodeContext } from './contracts'
import { advances, closeFrame } from './frames'
import { frame, layout, node, slot } from './emit'
import { radixTrie } from './radix'
// DFS.lean recursive_refines_stack / entries_unique, Inline.lean inline_matches_recursive,
// ShapeRadix.lean radix_matches_signature and Positional.lean decode_encode_document /
// renumber_first_use checked before implementation.
export function encodeGraph(value: unknown): string {
  const context: EncodeContext = {
    bigints: undefined,
    boundaries: [],
    descriptors: [],
    hasBuffers: false,
    ids: new Map(),
    layoutRoot: radixTrie(),
    layouts: [],
    owners: undefined,
    payloads: [],
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
    for (const [parameters, owner] of context.owners) {
      payloads[parameters] = [owner]
      descriptors[parameters] = layout(11, undefined, -1, context)
    }
  return documentText(context)
}
// The root is one slot: a literal document, returned as text, or node 0.
function enter(value: unknown, context: EncodeContext): string | undefined {
  if (value !== null && typeof value === 'object') {
    node(value, context)
    return undefined
  }
  const root = frame(-1, -1, undefined, value)
  root.row = []
  slot(root, value, context)
  if (!root.reference) return JSON.stringify(root.row)
  context.top = 0
  return undefined
}
// Positional.lean renumber_first_use: interning the provisional ids in node order yields the
// first-use layout table.
function documentText(context: EncodeContext): string {
  const { descriptors, layouts: provisional, shapes } = context
  const payloads = context.payloads as Row[]
  const order = new Array<number>(provisional.length).fill(-1)
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
  if (!context.hasBuffers) return JSON.stringify([shapes, layouts, descriptors, payloads])
  // Base64 needs no escaping, so buffer payloads skip the serializer's string scan; the payloads
  // between them are serialized together.
  const parts: string[] = []
  let start = 0
  for (let index = 0; index < payloads.length; index++)
    if (layouts[descriptors[index]][0] === 7) {
      if (index > start) parts.push(JSON.stringify(payloads.slice(start, index)).slice(1, -1))
      parts.push('["' + (payloads[index][0] as string) + '"]')
      start = index + 1
    }
  if (start < payloads.length) parts.push(JSON.stringify(payloads.slice(start)).slice(1, -1))
  const tables = JSON.stringify([shapes, layouts, descriptors])
  return tables.slice(0, -1) + ',[' + parts.join(',') + ']]'
}
