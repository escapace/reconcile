import type { EncodeContext, Frame } from './contracts'
// Inline.lean inline_step_refines / inline_matches_recursive: containers write children in
// place and yield after a child pushed its frame. Positional.lean sparse_roundtrip covers the
// incremental presence runs. Dynamic observations and IteratorClose are runtime obligations
// (docs/lean.md, serialization) checked by differential tests.
import { encodeFail as fail, int, maxArrayLength } from './common'
import { readView, readURL } from './native'
import { leafCaptures } from './leaf'
import { lengths } from './layout'
import { node, slot } from './emit'
import { intern } from './radix'
import { openBuiltin, closeIteratorAfterThrow, hasElement } from '../standard-prototypes'

const object = (value: unknown): value is Record<PropertyKey, unknown> =>
  value !== null && (typeof value === 'object' || typeof value === 'function')
// True when the last slot pushed a frame that must complete first.
const pushed = (frame: Frame, context: EncodeContext) =>
  context.stack[context.stack.length - 1] !== frame
export function closeFrame(frame: Frame) {
  if (frame.active) {
    frame.active = false
    // Cleanup only handles an existing throw; return result cannot replace it.
    closeIteratorAfterThrow(frame.iterator)
  }
}
// Appends one present element. Positional.lean presenceGo: a gap records the boundaries of the
// whole hole run at once.
function append(frame: Frame, context: EncodeContext, index: number, item: unknown) {
  if (index !== frame.end) (frame.holes ??= []).push(frame.end, index)
  frame.end = index + 1
  if (frame.length <= index) frame.length = index + 1
  slot(frame, item, context)
}
function array(frame: Frame, context: EncodeContext) {
  if (frame.phase === 0) startArray(frame)
  const value = frame.value as unknown[]
  // The cursor stays local in the hole-scanning loop; it is stored only when yielding.
  for (let index = frame.index; index < value.length; index++) {
    if (index >= maxArrayLength) fail('array length or index invalid')
    if (hasElement(value, index)) {
      append(frame, context, index, value[index])
      if (pushed(frame, context)) {
        frame.index = index + 1
        return false
      }
    }
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
  frame.iterator = opened.iterator as Frame['iterator']
  frame.step = opened.step
  frame.active = false
}
function leaf(frame: Frame, context: EncodeContext) {
  frame.row = leafCaptures[frame.tag]!(frame.value, context, frame.detail)
  return true
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
  frame.active = false // step/done/value failures do not close this iterator.
  const result: unknown =
    frame.step === undefined
      ? Reflect.apply(frame.next, frame.iterator, [])
      : frame.step(frame.iterator)
  if (!object(result)) throw new TypeError('iterator result is not an object')
  const done = Boolean(result.done)
  if (done) return false
  frame.child = result.value
  frame.active = true
  return true
}
function record(frame: Frame, context: EncodeContext) {
  if (frame.phase === 0) {
    const names = Object.getOwnPropertyNames(frame.value)
    // deserialize restores enumerable properties only, so a hidden property is rejected, not
    // revealed.
    if (Object.keys(frame.value).length !== names.length) fail('non-enumerable property')
    frame.keys = names
    // The shape id is the record layout's key field.
    frame.detail = intern(context.shapeRoot, context.shapes, frame.keys)
    frame.row = []
    frame.index = 0
    frame.phase = 1
  }
  const keys = frame.keys
  while (frame.index < keys.length) {
    slot(frame, Reflect.get(frame.value, keys[frame.index++]), context)
    if (pushed(frame, context)) return false
  }
  if (Object.getOwnPropertySymbols(frame.value).length !== 0) fail('symbol key')
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
function startArray(frame: Frame) {
  if (!Array.isArray(frame.value)) fail('array brand')
  const initial = (frame.value as unknown[]).length
  if (!int(initial, maxArrayLength)) fail('array length or index invalid')
  frame.length = initial
  frame.index = 0
  frame.row = []
  frame.phase = 1
}
function url(frame: Frame, context: EncodeContext) {
  if (frame.phase === 0) {
    frame.state = readURL(frame.value) as Frame['state']
    frame.phase = 1
    frame.input = node(frame.state.parameters, context)
    if (pushed(frame, context)) return false
  }
  ;(context.owners ??= new Map()).set(frame.input, frame.id)
  frame.row = [frame.state.href]
  return true
}
function view(frame: Frame, context: EncodeContext) {
  if (frame.phase === 0) {
    frame.state = readView(frame.value, frame.detail) as Frame['state']
    frame.phase = 1
    frame.input = node(frame.state.buffer, context)
    if (pushed(frame, context)) return false
  }
  frame.row = [frame.input, frame.state.byteOffset, frame.state.length]
  return true
}
// Indexed by node tag; leaf tags are captured on discovery and never pushed.
export const advances = [
  record,
  record,
  array,
  array,
  map,
  set,
  leaf,
  leaf,
  view,
  url,
  leaf,
  leaf,
  leaf,
]
