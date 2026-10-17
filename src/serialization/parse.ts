import type { DecodeContext, Row } from './contracts'
import { decoders } from './facets/decode'
import { int, decodeFail as fail, literal } from './common'
import { keyed, slotted } from './layout'
import { intern, radixTrie } from './radix'
import type { RadixNode } from './radix'
import { temporalKinds, validViewKind } from './facets/native'
// Positional.lean encode_decode_document: distinct first-use tables, typed references and
// canonical slots and runs accept exactly the encoder's documents for the decoded node list;
// Preorder.lean check_iff fixes the node numbering to the encoder's.
export function decodeGraph(text: string): unknown {
  if (typeof text !== 'string') fail('text')
  const document: unknown = JSON.parse(text)
  if (!Array.isArray(document)) fail('envelope')
  // A root without nodes is one literal.
  if (document.length === 1) return literal(document[0])
  if (!envelope(document)) fail('envelope')
  const shapes = checkShapes(document[0] as unknown[])
  const layouts = document[1] as number[][]
  checkLayouts(layouts, shapes.length)
  const payloads = document[3] as Row[]
  const context: DecodeContext = {
    bigints: undefined,
    cursor: 0,
    ends: new Array<number>(payloads.length),
    layouts,
    nodeLayouts: new Array<number[]>(payloads.length),
    output: new Array<unknown>(payloads.length),
    owned: 0,
    parameters: undefined,
    payloads,
    scalars: 0,
    shapes,
    urls: 0,
  }
  checkDescriptors(document[2] as unknown[], context)
  allocate(context)
  fill(context)
  return context.output[0]
}
function envelope(document: unknown[]): boolean {
  return (
    document.length === 4 &&
    Array.isArray(document[0]) &&
    Array.isArray(document[1]) &&
    Array.isArray(document[2]) &&
    Array.isArray(document[3]) &&
    document[3].length !== 0 &&
    document[2].length === document[3].length
  )
}
// Fresh natives and empty containers first, then dependent natives against their typed targets.
function allocate(context: DecodeContext): void {
  const { nodeLayouts, output, payloads } = context
  for (let index = 0; index < payloads.length; index++)
    output[index] = decoders[nodeLayouts[index][0]].allocate(
      payloads[index],
      nodeLayouts[index],
      context,
    )
  for (let index = 0; index < payloads.length; index++) {
    const link = decoders[nodeLayouts[index][0]].link
    if (link !== undefined)
      output[index] = link(payloads[index], nodeLayouts[index], context, index)
  }
  if (context.owned !== context.urls) fail('params owner')
}
// Positional.lean firstUse: each node's layout id is a used one or the next new one, and every
// layout is used.
function checkDescriptors(descriptors: unknown[], context: DecodeContext): void {
  const { layouts, nodeLayouts, payloads } = context
  let used = 0
  for (let index = 0; index < payloads.length; index++) {
    const id = descriptors[index]
    if (!int(id, used) || id >= layouts.length) fail('layout order')
    if (id === used) used++
    nodeLayouts[index] = layouts[id]
    if (!Array.isArray(payloads[index])) fail('payload')
  }
  if (used !== layouts.length) fail('unused layout')
}
// Preorder.lean check_iff: filling in reverse records each node's subtree end; the root's must
// cover every node, so all nodes are reachable and numbered in depth-first entry order.
function fill(context: DecodeContext): void {
  const { ends, nodeLayouts, output, payloads } = context
  for (let index = payloads.length - 1; index >= 0; index--) {
    context.cursor = index + 1
    const layout = nodeLayouts[index]
    decoders[layout[0]].fill?.(payloads[index], output[index], layout, context, index)
    ends[index] = context.cursor
  }
  if (ends[0] !== payloads.length) fail('node order')
}
// Shapes are distinct lists of distinct keys. Key order is not checked: a proxy's ownKeys may
// list names before indices, and the decoder defines keys in the listed order.
function checkShapes(shapes: unknown[]): string[][] {
  const root = radixTrie<string>()
  const interned: string[][] = []
  // The shape that last listed each key: a repeat within one shape finds its own index.
  const last = new Map<string, number>()
  for (let index = 0; index < shapes.length; index++) {
    const keys = shapes[index]
    if (!Array.isArray(keys)) fail('shape')
    for (const key of keys as unknown[]) {
      if (typeof key !== 'string' || last.get(key) === index) fail('shape key')
      last.set(key, index)
    }
    if (intern(root, interned, keys as string[]) !== index) fail('duplicate shape')
  }
  return interned
}
// Layouts are distinct and use shapes in first-use order. Each node checks its layout's runs
// against its own payload.
function checkLayouts(layouts: unknown[], shapeCount: number): void {
  const root = radixTrie<number>()
  const interned: number[][] = []
  let shapes = 0
  for (let index = 0; index < layouts.length; index++) {
    const layout = layouts[index]
    if (!Array.isArray(layout) || !int(layout[0], decoders.length - 1)) fail('layout')
    const tag = layout[0]
    if (keyed(tag)) shapes = checkKey(tag, layout[1], shapes, shapeCount)
    if (!slotted(tag) && layout.length !== (keyed(tag) ? 2 : 1)) fail('layout')
    distinct(root, interned, layout as unknown[], index)
  }
  if (shapes !== shapeCount) fail('unused shape')
}
// Every entry is a control integer, and no layout repeats an earlier one.
function distinct(
  root: RadixNode<number>,
  interned: number[][],
  layout: unknown[],
  index: number,
): void {
  for (const key of layout) if (!int(key)) fail('layout')
  if (intern(root, interned, layout as number[]) !== index) fail('duplicate layout')
}
// Returns the number of shapes used so far.
function checkKey(tag: number, key: unknown, shapes: number, shapeCount: number): number {
  if (tag <= 1) {
    if (!int(key, shapes) || key >= shapeCount) fail('shape order')
    return key === shapes ? shapes + 1 : shapes
  }
  if (tag === 8 ? !validViewKind(key) : !int(key, temporalKinds - 1)) fail('layout key')
  return shapes
}
