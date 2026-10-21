import type { Row, Frame, EncodeContext } from './contracts'
import { leafCaptures } from './leaf'
import { recognize } from './facets/index'
import { encodeFail as fail } from './common'
import { keyed } from './layout'
import { intern, lookup } from './radix'
import { sparseArray } from '../standard-prototypes'
// Positional.lean encodeSlots / layoutOf: every value position is a slot. Its kind, literal or
// reference, is recorded only where it changes, as the run boundary at the slot's position.
export function slot(frame: Frame, item: unknown, context: EncodeContext): void {
  switch (typeof item) {
    case 'bigint':
      return push(frame, bigint(item, context), true, context)
    case 'boolean':
    case 'string':
      return push(frame, item, false, context)
    case 'number':
      // JSON numbers are finite and never -0; every other number is a shared node.
      return item - item === 0 && (item !== 0 || 1 / item > 0)
        ? push(frame, item, false, context)
        : push(frame, special(item, context), true, context)
    case 'object':
      return item === null
        ? push(frame, null, false, context)
        : push(frame, node(item, context), true, context)
    case 'undefined':
      return push(frame, scalar(13, context), true, context)
    default:
      fail('unsupported value')
  }
}
// Frames complete in stack order, so a frame's boundaries are the top of one per-call stack
// from its first boundary until it completes.
function push(frame: Frame, value: unknown, reference: boolean, context: EncodeContext): void {
  const row = frame.row
  if (reference !== frame.reference) {
    if (frame.runs < 0) frame.runs = context.top
    context.boundaries[context.top++] = row.length
    frame.reference = reference
  }
  row.push(value)
}
function special(item: number, context: EncodeContext): number {
  const tag = Number.isNaN(item) ? 14 : item === Infinity ? 15 : item === -Infinity ? 16 : 17
  return scalar(tag, context)
}
// Shared scalar nodes: undefined, NaN, Infinity, -Infinity and -0 by tag, bigints by value. A
// bigint is its sign, `0x` and lowercase hexadecimal digits (Size.lean encodeInt), which convert
// in linear time, unlike decimal; the prefix lets BigInt read the text without a copy.
function bigint(item: bigint, context: EncodeContext): number {
  let id = (context.bigints ??= new Map<bigint, number>()).get(item)
  if (id === undefined) {
    id = leaf([item < 0n ? `-0x${(-item).toString(16)}` : `0x${item.toString(16)}`], 18, context)
    context.bigints.set(item, id)
  }
  return id
}
function leaf(payload: Row, tag: number, context: EncodeContext): number {
  const id = context.payloads.length
  context.payloads.push(payload)
  context.descriptors.push(layout(tag, undefined, -1, context))
  return id
}
// Each constant node has its own empty payload, so the returned data holds no array twice and
// none from another call.
function scalar(tag: number, context: EncodeContext): number {
  return ((context.scalars ??= sparseArray())[tag] ??= leaf([], tag, context))
}
// Interns [tag, key?, ...runs] with provisional ids in completion order, the runs being the
// lengths between boundaries[from ..< top]; Positional.lean renumber_first_use renumbers them.
export function layout(
  tag: number,
  detail: number | undefined,
  from: number,
  context: EncodeContext,
): number {
  // A layout without runs is identified by its tag and key alone. For one tag it is shorter
  // than every layout with runs, so the two never coincide.
  if (from < 0) {
    const byKey = ((context.plain ??= sparseArray())[tag] ??= sparseArray())
    const key = keyed(tag) ? detail! : 0
    let id = byKey[key]
    if (id === undefined) {
      id = byKey[key] = context.layouts.length
      context.layouts.push(keyed(tag) ? [tag, detail!] : [tag])
    }
    return id
  }
  // The key is built in a per-call scratch array and copied only when it is new.
  const key = context.scratch
  key[0] = tag
  let length = 1
  if (keyed(tag)) key[length++] = detail!
  const boundaries = context.boundaries
  for (let index = from; index < context.top; index++)
    key[length++] = boundaries[index] - (index > from ? boundaries[index - 1] : 0)
  context.top = from
  const id = lookup(context.layoutRoot, key, length)
  return id >= 0 ? id : intern(context.layoutRoot, context.layouts, key.slice(0, length))
}
// Identity is reserved on discovery; containers push a frame, leaves are captured at once.
export function node(item: object, context: EncodeContext): number {
  let id = context.ids.get(item)
  if (id === undefined) {
    const { descriptors, payloads } = context
    id = payloads.length
    context.ids.set(item, id)
    payloads.push(undefined)
    descriptors.push(-1)
    const kind = recognize(item)
    const captureLeaf = leafCaptures[kind.tag]
    if (captureLeaf === undefined) context.stack.push(frame(id, kind.tag, kind.detail, item))
    else {
      payloads[id] = captureLeaf(item, context, kind.detail)
      descriptors[id] = layout(kind.tag, kind.detail, -1, context)
    }
  }
  return id
}
// Every frame starts with one field layout so the traversal stays monomorphic.
export function frame(id: number, tag: number, detail: number | undefined, value: unknown): Frame {
  return {
    active: false,
    child: undefined,
    detail,
    end: 0,
    holes: undefined,
    id,
    index: 0,
    input: 0,
    iterator: undefined,
    keys: undefined,
    length: 0,
    mapValue: undefined,
    native: false,
    next: undefined,
    phase: 0,
    reference: false,
    row: undefined,
    runs: -1,
    state: undefined,
    tag,
    value,
  } as unknown as Frame
}
