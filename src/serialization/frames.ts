import type { Frame, EncodeContext } from './contracts'
// Inline.lean inline_step_refines / inline_matches_recursive: containers tokenize children in
// place and yield after a child pushed its frame. Inline.lean direct_rows_exact covers the
// array row layout. Dynamic observations and IteratorClose rest on the local simulation in
// lean/Serialization/ENCODER.md and remain differential-test obligations.
import { encodeFail as fail, int, maxArrayLength } from './common'
import { readView, readURL } from './native'
import { leafCaptures } from './leaf'

const object = (value: unknown): value is Record<PropertyKey, unknown> =>
  value !== null && (typeof value === 'object' || typeof value === 'function')
// True when tokenizing the last child pushed a frame that must complete first.
const pushed = (frame: Frame, context: EncodeContext) =>
  context.stack[context.stack.length - 1] !== frame
export function closeFrame(frame: Frame) {
  if (frame.active) {
    frame.active = false
    const method = frame.iterator.return
    if (method != null) Reflect.apply(method as Frame['next'], frame.iterator, [])
    // Cleanup only handles an existing throw; return result cannot replace it.
  }
}
// Appends one present element: densely while indices stay consecutive, otherwise as a pair.
function append(frame: Frame, index: number, item: unknown) {
  if (frame.dense && frame.row.length === index + 2) frame.row.push(item)
  else {
    sparseRow(frame)
    frame.row.push(index, item)
  }
  if (frame.length <= index) frame.length = index + 1
}
function array(frame: Frame, context: EncodeContext) {
  if (frame.phase === 0) startArray(frame)
  const value = frame.value as unknown[]
  // The cursor stays local in the hole-scanning loop; it is stored only when yielding.
  for (let index = frame.index; index < value.length; index++) {
    if (index >= maxArrayLength) fail('array length or index invalid')
    if (index in value) {
      append(frame, index, context.token(value[index]))
      if (pushed(frame, context)) {
        frame.index = index + 1
        return false
      }
    }
  }
  if (frame.dense && frame.row.length !== frame.length + 2) sparseRow(frame)
  frame.row[1] = frame.length
  return true
}
function iterator(frame: Frame, iterable: Iterable<unknown>) {
  const current: unknown = Reflect.apply(iterable[Symbol.iterator], iterable, [])
  if (!object(current)) throw new TypeError('iterator is not an object')
  frame.iterator = current as Frame['iterator']
  frame.next = current.next as Frame['next'] // GetIterator caches next once, without testing callability.
  frame.active = false
}
function leaf(frame: Frame, context: EncodeContext) {
  frame.row = leafCaptures[frame.tag]!(frame.value, context, frame.detail)
  return true
}
function map(frame: Frame, context: EncodeContext) {
  if (frame.phase === 0) {
    frame.row = [4]
    iterator(frame, (frame.value as Map<unknown, unknown>).entries())
    frame.phase = 1
  } else if (frame.phase === 2) {
    frame.phase = 1
    frame.row.push(context.token(frame.mapValue))
    if (pushed(frame, context)) return false
  }
  while (next(frame)) {
    // Native destructuring closes the entry iterator before either child is traversed.
    const [key, value] = frame.child as Iterable<unknown>
    frame.row.push(context.token(key))
    if (pushed(frame, context)) {
      frame.mapValue = value
      frame.phase = 2
      return false
    }
    frame.row.push(context.token(value))
    if (pushed(frame, context)) return false
  }
  return true
}
function next(frame: Frame) {
  frame.active = false // step/done/value failures do not close this iterator.
  const result: unknown = Reflect.apply(frame.next, frame.iterator, [])
  if (!object(result)) throw new TypeError('iterator result is not an object')
  const done = Boolean(result.done)
  if (done) return false
  frame.child = result.value
  frame.active = true
  return true
}
function record(frame: Frame, context: EncodeContext) {
  if (frame.phase === 0) {
    frame.keys = Object.getOwnPropertyNames(frame.value)
    frame.row = [frame.tag, context.shape(frame.keys)]
    frame.index = 0
    frame.phase = 1
  }
  const keys = frame.keys
  while (frame.index < keys.length) {
    frame.row.push(context.token(Reflect.get(frame.value, keys[frame.index++])))
    if (pushed(frame, context)) return false
  }
  if (Object.getOwnPropertySymbols(frame.value).length !== 0) fail('symbol key')
  return true
}
function set(frame: Frame, context: EncodeContext) {
  if (frame.phase === 0) {
    frame.row = [5]
    iterator(frame, (frame.value as Set<unknown>).values())
    frame.phase = 1
  }
  while (next(frame)) {
    frame.row.push(context.token(frame.child))
    if (pushed(frame, context)) return false
  }
  return true
}
// Rewrites a dense row prefix [2, _, v0, v1, ...] as sparse [3, _, 0, v0, 1, v1, ...].
function sparseRow(frame: Frame) {
  if (!frame.dense) return
  const dense = frame.row
  const sparse: unknown[] = [3, 0]
  for (let index = 2; index < dense.length; index++) sparse.push(index - 2, dense[index])
  frame.row = sparse
  frame.dense = false
}
function startArray(frame: Frame) {
  if (!Array.isArray(frame.value)) fail('array brand')
  const initial = (frame.value as unknown[]).length
  if (!int(initial, maxArrayLength)) fail('array length or index invalid')
  frame.length = initial
  frame.index = 0
  frame.dense = true
  frame.row = [2, 0]
  frame.phase = 1
}
function url(frame: Frame, context: EncodeContext) {
  if (frame.phase === 0) {
    frame.state = readURL(frame.value) as Frame['state']
    frame.phase = 1
    frame.input = context.token(frame.state.parameters)
    if (pushed(frame, context)) return false
  }
  context.owner(-(frame.input as number) - 6, context.ids.get(frame.value)!)
  frame.row = [9, frame.state.href]
  return true
}
function view(frame: Frame, context: EncodeContext) {
  if (frame.phase === 0) {
    frame.state = readView(frame.value, frame.detail) as Frame['state']
    frame.phase = 1
    frame.input = context.token(frame.state.buffer)
    if (pushed(frame, context)) return false
  }
  frame.row = [8, frame.detail, frame.input, frame.state.byteOffset, frame.state.length]
  return true
}
export const advances = [record, record, array, array, map, set, leaf, leaf, view, url, leaf, leaf]
