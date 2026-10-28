import type { DecodeContext, Row } from './contracts'
import { decoders } from './facets/decode'
import { int, decodeFail as fail } from './common'
import { keyed, slotted } from './layout'
import { temporalKinds, validViewKind } from './facets/native'
import { charge, chargeLiteral, stringWords } from './size'
import { checkBytes, decodeBytes } from './binary'
import { deserializeLimitExceeded } from '../error'
import { denseArray } from '../standard-prototypes'
// The value the document encodes. Decoding writes decoded values into the document's rows.
export function decodeGraph(document: unknown, maxBytes: number): unknown {
  return decodeDocument(document, maxBytes, false, decodeBytes)
}
// The words `decodeGraph` charges under a finite limit, with the same checks and charges in the
// same order (Size.lean accepts_iff_bytes: eight bytes per word is the smallest accepted limit).
// Nothing is written into the document, so it can still be decoded.
export function measureGraph(document: unknown, maxBytes: number): number {
  return decodeDocument(document, maxBytes, true, checkBytes) as number
}
function createContext(
  control: unknown[],
  payloads: Row[],
  limit: number,
  maxBytes: number,
  limited: boolean,
  measuring: boolean,
  bytes: DecodeContext['bytes'],
): DecodeContext {
  return {
    bytes,
    control,
    cursor: 0,
    ends: denseArray<number>(payloads.length),
    limit,
    limited,
    maxBytes,
    measuring,
    nodeLayouts: denseArray<number>(payloads.length),
    output: denseArray<unknown>(payloads.length),
    owned: 0,
    parameters: undefined,
    payloads,
    shapes: [],
    urls: 0,
    weights: undefined,
    words: 0,
  }
}
// Positional.lean decode_encode_relaxed / decodeNodes_sound: every accepted document is the slot
// encoding of the nodes it decodes to, with runs and references checked. Tables are used as
// given; their order and distinctness are not checked. Preorder.lean check_iff makes every
// node reachable and numbered in depth-first entry order, so the size charges no unreachable node
// (Size.lean accounting_eq_reachable); the root slot is charged first.
// Returns the root, or while measuring the words charged.
function decodeDocument(
  document: unknown,
  maxBytes: number,
  measuring: boolean,
  bytes: DecodeContext['bytes'],
): unknown {
  if (!Array.isArray(document)) fail('envelope')
  const limit = Math.floor(maxBytes / 8)
  const limited = measuring || limit !== Infinity
  // A root without nodes is one literal: any JSON value, as JSON.parse produced it.
  if (document.length === 1) return literalRoot(document[0], limit, maxBytes, limited, measuring)
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
  // Size.lean node_count_le_accounting: a document has at most as many nodes as words, so its
  // tables are allocated only within the limit.
  if (payloads.length > limit) throw deserializeLimitExceeded(maxBytes)
  const context = createContext(control, payloads, limit, maxBytes, limited, measuring, bytes)
  if (limited) charge(context, 1)
  checkControl(context)
  allocate(context)
  // The root's own occurrence: a bigint root is charged its digits.
  if (context.weights !== undefined) charge(context, context.weights[0])
  fill(context)
  return measuring ? context.words : context.output[0]
}
// The root slot, then the literal where it occurs.
function literalRoot(
  literal: unknown,
  limit: number,
  maxBytes: number,
  limited: boolean,
  measuring: boolean,
): unknown {
  const budget = { limit, maxBytes, words: 0 }
  if (limited) {
    charge(budget, 1)
    chargeLiteral(budget, literal)
  }
  return measuring ? budget.words : literal
}

// Positional.lean decodeControl: each node's layout id, the number of shapes, each shape framed
// by its length, then each layout framed by its length to the end. Shapes and layouts are read
// in place by the offset of their first entry; the length precedes it.
function checkControl(context: DecodeContext): void {
  const { control, nodeLayouts, payloads } = context
  const count = control[payloads.length]
  if (!int(count)) fail('shapes')
  let at = payloads.length + 1
  for (let shape = 0; shape < count; shape++) at = checkShape(context, at)
  const layouts: number[] = []
  while (at < control.length) {
    const length = frameLength(control, at)
    checkLayout(control, at + 1, at + 1 + length, count)
    layouts.push(at + 1)
    at += length + 1
  }
  for (let index = 0; index < payloads.length; index++) {
    const id = control[index]
    if (!int(id, layouts.length - 1)) fail('layout id')
    nodeLayouts[index] = layouts[id]
    if (!Array.isArray(payloads[index])) fail('payload')
  }
}
// A shape: its keys, which must be strings, and under a limit their words. Returns the offset
// of the next frame. Whether `Object.prototype` holds a key is read here once per shape: on the
// documented input only built-in code and the global Temporal, if any, run before the records are
// filled, and a call must not change standard prototypes.
function checkShape(context: DecodeContext, at: number): number {
  const { control } = context
  const length = frameLength(control, at)
  let words = 0
  let inherits = false
  for (let index = at + 1; index <= at + length; index++) {
    const key = control[index]
    if (typeof key !== 'string') fail('shape key')
    if (context.limited) words += stringWords(key.length)
    if (!context.measuring && !inherits) inherits = key in Object.prototype
  }
  context.shapes.push(at + 1, inherits ? 1 : 0, words)
  return at + length + 1
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
  const key = keyed(tag)
  const runs = at + (key ? 2 : 1)
  if (key) checkKey(tag, control[at + 1], shapeCount)
  if (!slotted(tag) && stop !== runs) fail('layout')
  // checkKey validated a key; the runs after it must be integers.
  for (let index = runs; index < stop; index++) if (!int(control[index])) fail('layout')
}
// Fresh natives and empty containers first, then dependent natives against their typed targets.
function allocate(context: DecodeContext): void {
  const { control, nodeLayouts, output, payloads } = context
  for (let index = 0; index < payloads.length; index++) {
    const at = nodeLayouts[index]
    output[index] = decoders[control[at] as number].allocate(payloads[index], at, context, index)
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
