import type { EncodeContext, Frame } from './contracts'
// Inline.lean inline_step_refines / inline_matches_recursive: containers write children in
// place and yield after a child pushed its frame. Positional.lean sparse_roundtrip covers the
// incremental presence runs. Dynamic observations are runtime obligations (docs/lean.md,
// serialization) checked by differential tests.
import { encodeFail as fail, int, maxArrayLength } from './common'
import { readView, readURL } from './native'
import { lengths } from './layout'
import { layout, node, slot } from './emit'
import { intern } from './radix'
import { openBuiltin, hasElement } from '../standard-prototypes'
import { hasSymbolKey, hiddenNames } from '../object-property'

// Up to this many values, a row made at its length costs less than the first push, which in V8
// reserves 17 slots; beyond it a pushed row costs no more and stays packed, which JSON.stringify
// writes faster.
const presizedRow = 8
// True when the last slot pushed a frame that must complete first.
const pushed = (frame: Frame, context: EncodeContext) =>
  context.stack[context.stack.length - 1] !== frame
// Appends one present element. Positional.lean presenceGo: a gap records the boundaries of the
// whole hole run at once.
function append(frame: Frame, context: EncodeContext, index: number, item: unknown) {
  if (index !== frame.end) (frame.holes ??= []).push(frame.end, index)
  frame.end = index + 1
  if (frame.length <= index) frame.length = index + 1
  slot(frame, item, context)
}
function array(frame: Frame, context: EncodeContext) {
  const value = frame.value as unknown[]
  // The first bound is the length the start just read; an element read can change it, so each
  // later bound is read again. The cursor stays local in the hole-scanning loop; it is stored only
  // when yielding.
  let length = frame.phase === 0 ? startArray(frame) : value.length
  for (let index = frame.index; index < length; index++) {
    if (index >= maxArrayLength) fail('array length or index invalid')
    if (hasElement(value, index)) {
      append(frame, context, index, value[index])
      if (pushed(frame, context)) {
        frame.index = index + 1
        return false
      }
    }
    length = value.length
  }
  // A dense array is its values; a sparse one is [length, presence runs, values].
  if (frame.holes !== undefined || frame.end !== frame.length) {
    const holes = frame.holes ?? []
    if (frame.end < frame.length) holes.push(frame.end)
    frame.tag = 3
    frame.row = [frame.length, lengths(holes), frame.row]
  }
  return true
}
// Opens the built-in iterator of a `Map`'s entries or a `Set`'s members, stepped by the built-in
// `next`; its steps are fresh native results, which nothing can observe.
function builtinIterator(frame: Frame, collection: object, map: boolean) {
  const opened = openBuiltin(collection, map, map ? 'entries' : 'values')
  frame.iterator = opened.iterator
  frame.step = opened.step
}
function map(frame: Frame, context: EncodeContext) {
  if (frame.phase === 0) {
    frame.row = []
    // The built-in iterator, fresh and native.
    builtinIterator(frame, frame.value, true)
    frame.phase = 1
  } else if (frame.phase === 2) {
    frame.phase = 1
    slot(frame, frame.mapValue, context)
    if (pushed(frame, context)) return false
  }
  while (next(frame)) {
    // A native Map iterator yields fresh [key, value] arrays, read by index.
    const key = (frame.child as readonly unknown[])[0]
    const value = (frame.child as readonly unknown[])[1]
    slot(frame, key, context)
    if (pushed(frame, context)) {
      frame.mapValue = value
      frame.phase = 2
      return false
    }
    slot(frame, value, context)
    if (pushed(frame, context)) return false
  }
  return true
}
function next(frame: Frame) {
  const result = frame.step(frame.iterator)
  if (result.done === true) return false
  frame.child = result.value
  return true
}
function record(frame: Frame, context: EncodeContext) {
  if (frame.phase === 0) {
    const names = Object.getOwnPropertyNames(frame.value)
    // deserialize restores enumerable properties only, so a hidden property is rejected, not
    // revealed.
    if (hiddenNames(frame.value, names, true) !== undefined) fail('non-enumerable property')
    frame.keys = names
    // The shape id is the record layout's key field.
    frame.detail = intern(context.shapeRoot, context.shapes, frame.keys)
    // push writes every index of a short row before the row is read, so no hole is read; a
    // longer row grows by push.
    frame.row = names.length <= presizedRow ? new Array(names.length) : []
    frame.phase = 1
  }
  const keys = frame.keys
  while (frame.index < keys.length) {
    slot(frame, Reflect.get(frame.value, keys[frame.index++]), context)
    if (pushed(frame, context)) return false
  }
  if (hasSymbolKey(frame.value)) fail('symbol key')
  return true
}
function set(frame: Frame, context: EncodeContext) {
  if (frame.phase === 0) {
    frame.row = []
    builtinIterator(frame, frame.value, false)
    frame.phase = 1
  }
  while (next(frame)) {
    slot(frame, frame.child, context)
    if (pushed(frame, context)) return false
  }
  return true
}
// Starts an array frame and returns the length it read.
function startArray(frame: Frame): number {
  const initial = (frame.value as unknown[]).length
  if (!int(initial, maxArrayLength)) fail('array length or index invalid')
  frame.length = initial
  frame.row = []
  frame.phase = 1
  return initial
}
// A URL's `searchParams` is restored from the URL, so its node, reserved here unless another
// reference met it first, records only its owner.
function url(frame: Frame, context: EncodeContext) {
  frame.state = readURL(frame.value) as Frame['state']
  const { descriptors, ids, payloads } = context
  const parameters = frame.state.parameters
  let id = ids.get(parameters)
  if (id === undefined) {
    id = payloads.length
    ids.set(parameters, id)
    payloads.push(undefined)
    descriptors.push(-1)
  }
  payloads[id] = [frame.id]
  descriptors[id] = layout(11, undefined, -1, context)
  frame.row = [frame.state.href]
  return true
}
function view(frame: Frame, context: EncodeContext) {
  if (frame.phase === 0) {
    frame.state = readView(frame.value, frame.detail) as Frame['state']
    // deserialize builds a view over a standard buffer, so a view over another one is rejected.
    if (Object.getPrototypeOf(frame.state.buffer) !== ArrayBuffer.prototype)
      fail('unsupported prototype')
    frame.phase = 1
    frame.input = node(frame.state.buffer, context)
    if (pushed(frame, context)) return false
  }
  frame.row = [frame.input, frame.state.byteOffset, frame.state.length]
  return true
}
// Indexed by the tag of a pushed frame: a record, an array, a Map, a Set, a view or a URL. A leaf
// is captured on discovery and never pushed, and a sparse array takes its tag on completion, so
// those tags have no advance; every tag has an own element, so no lookup reaches
// `Array.prototype`.
export const advances: ReadonlyArray<
  ((frame: Frame, context: EncodeContext) => boolean) | undefined
> = /* @__PURE__ */ Object.freeze([
  record,
  record,
  array,
  undefined,
  map,
  set,
  undefined,
  undefined,
  view,
  url,
])
