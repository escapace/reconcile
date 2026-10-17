import type { DecodeContext, Row } from './contracts'
import { decoders } from './facets/decode'
import { int, decodeFail as fail, literal } from './common'
import { keyed, slotted } from './layout'
import { temporalKinds, validViewKind } from './facets/native'
// Positional.lean decode_encode_relaxed / decodeNodes_sound: every accepted document is the slot
// encoding of the nodes it decodes to, with runs and references checked. Tables are used as
// given; their order and distinctness are not checked. Preorder.lean check_iff makes every
// node reachable and numbered in depth-first entry order.
export function decodeGraph(text: string): unknown {
  if (typeof text !== 'string') fail('text')
  const document: unknown = JSON.parse(text)
  if (!Array.isArray(document)) fail('envelope')
  // A root without nodes is one literal.
  if (document.length === 1) return literal(document[0])
  const control = document[0] as unknown[]
  const payloads = document[1] as Row[]
  if (
    document.length !== 2 ||
    !Array.isArray(control) ||
    !Array.isArray(payloads) ||
    payloads.length === 0 ||
    control.length <= payloads.length
  )
    fail('envelope')
  const context: DecodeContext = {
    control,
    cursor: 0,
    ends: new Array<number>(payloads.length),
    nodeLayouts: new Array<number>(payloads.length),
    output: new Array<unknown>(payloads.length),
    owned: 0,
    parameters: undefined,
    payloads,
    shapes: [],
    urls: 0,
  }
  checkControl(context)
  allocate(context)
  fill(context)
  return context.output[0]
}
// Positional.lean decodeControl: each node's layout id, the number of shapes, each shape framed
// by its length, then each layout framed by its length to the end. Shapes and layouts are read
// in place by the offset of their first entry; the length precedes it.
function checkControl(context: DecodeContext): void {
  const { control, nodeLayouts, payloads, shapes } = context
  const count = control[payloads.length]
  if (!int(count)) fail('shapes')
  let at = payloads.length + 1
  for (let shape = 0; shape < count; shape++) {
    const length = frameLength(control, at)
    for (let index = at + 1; index <= at + length; index++)
      if (typeof control[index] !== 'string') fail('shape key')
    shapes.push(at + 1)
    at += length + 1
  }
  const layouts: number[] = []
  while (at < control.length) {
    checkLayout(control, at + 1, at + 1 + frameLength(control, at), shapes.length)
    layouts.push(at + 1)
    at += (control[at] as number) + 1
  }
  for (let index = 0; index < payloads.length; index++) {
    const id = control[index]
    if (!int(id, layouts.length - 1)) fail('layout id')
    nodeLayouts[index] = layouts[id]
    if (!Array.isArray(payloads[index])) fail('payload')
  }
}
function frameLength(control: unknown[], at: number): number {
  const length = control[at]
  if (!int(length, control.length - at - 1)) fail('frame')
  return length
}
// A layout is [tag, key?, ...runs] of control integers; each payload checks its own runs.
function checkKey(tag: number, key: unknown, shapeCount: number): void {
  if (
    tag <= 1
      ? !int(key, shapeCount - 1)
      : tag === 8
        ? !validViewKind(key)
        : !int(key, temporalKinds - 1)
  )
    fail('layout key')
}
function checkLayout(control: unknown[], at: number, stop: number, shapeCount: number): void {
  const tag = control[at]
  if (stop === at || !int(tag, decoders.length - 1)) fail('layout')
  if (keyed(tag)) checkKey(tag, control[at + 1], shapeCount)
  if (!slotted(tag) && stop !== at + (keyed(tag) ? 2 : 1)) fail('layout')
  for (let index = at + 1; index < stop; index++) if (!int(control[index])) fail('layout')
}
// Fresh natives and empty containers first, then dependent natives against their typed targets.
function allocate(context: DecodeContext): void {
  const { control, nodeLayouts, output, payloads } = context
  for (let index = 0; index < payloads.length; index++) {
    const at = nodeLayouts[index]
    output[index] = decoders[control[at] as number].allocate(payloads[index], at, context)
  }
  for (let index = 0; index < payloads.length; index++) {
    const at = nodeLayouts[index]
    const link = decoders[control[at] as number].link
    if (link !== undefined) output[index] = link(payloads[index], at, context, index)
  }
  if (context.owned !== context.urls) fail('params owner')
}
// Preorder.lean check_iff: filling in reverse records each node's subtree end; the root's must
// cover every node, so all nodes are reachable and numbered in depth-first entry order.
function fill(context: DecodeContext): void {
  const { control, ends, nodeLayouts, output, payloads } = context
  for (let index = payloads.length - 1; index >= 0; index--) {
    context.cursor = index + 1
    const at = nodeLayouts[index]
    decoders[control[at] as number].fill?.(payloads[index], output[index], at, context, index)
    ends[index] = context.cursor
  }
  if (ends[0] !== payloads.length) fail('node order')
}
