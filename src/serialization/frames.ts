import type { Frame, EncodeContext } from './contracts'
// Refinement.lean: indexed_step_exact / indexed_run_exact; dynamic observations
// and native IteratorClose remain differential-test obligations.
import { encodeFail as fail, int, maxArrayLength } from './common'
import { readView, readURL } from './native'
import { leafCaptures } from './leaf'

const object = (value: unknown): value is Record<PropertyKey, unknown> =>
  value !== null && (typeof value === 'object' || typeof value === 'function')
export function closeFrame(frame: Frame) {
  if (frame.active) {
    frame.active = false
    const method = frame.iterator.return
    if (method != null) Reflect.apply(method as Frame['next'], frame.iterator, [])
    // Cleanup only handles an existing throw; return result cannot replace it.
  }
}
function acceptArrayChild(frame: Frame) {
  if (frame.dense && frame.index === frame.entries.length) frame.entries.push(frame.input)
  else {
    sparseEntries(frame)
    frame.entries.push(frame.index, frame.input)
  }
  frame.length = Math.max(frame.length, frame.index + 1)
  frame.index++
}
function array(frame: Frame, _context: EncodeContext) {
  if (frame.phase === 0) startArray(frame)
  else acceptArrayChild(frame)
  for (; frame.index < (frame.value as unknown[]).length; frame.index++) {
    if (frame.index >= maxArrayLength) fail('array length or index invalid')
    if (frame.index in frame.value) {
      frame.child = (frame.value as unknown[])[frame.index]
      return false
    }
  }
  if (frame.dense && frame.entries.length === frame.length)
    frame.row = [2, frame.length, ...frame.entries]
  else {
    sparseEntries(frame)
    frame.row = [3, frame.length, ...frame.entries]
  }
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
function map(frame: Frame) {
  if (frame.phase === 0) {
    frame.row = [4]
    iterator(frame, (frame.value as Map<unknown, unknown>).entries())
    frame.phase = 1
  } else if (frame.phase === 2) {
    frame.row.push(frame.input)
    frame.child = frame.mapValue
    frame.phase = 3
    return false
  } else if (frame.phase === 3) {
    frame.row.push(frame.input)
    frame.phase = 1
  }
  if (!next(frame)) return true
  // Native destructuring closes the entry iterator before either child is traversed.
  const [key, value] = frame.child as Iterable<unknown>
  frame.mapValue = value
  frame.child = key
  frame.phase = 2
  return false
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
  } else frame.row.push(frame.input)
  if (frame.index < frame.keys.length) {
    frame.child = Reflect.get(frame.value, frame.keys[frame.index++])
    return false
  }
  if (Object.getOwnPropertySymbols(frame.value).length !== 0) fail('symbol key')
  return true
}
function set(frame: Frame) {
  if (frame.phase === 0) {
    frame.row = [5]
    iterator(frame, (frame.value as Set<unknown>).values())
    frame.phase = 1
  } else frame.row.push(frame.input)
  return !next(frame)
}
function sparseEntries(frame: Frame) {
  if (!frame.dense) return
  const sparse = []
  for (let index = 0; index < frame.entries.length; index++)
    sparse.push(index, frame.entries[index])
  frame.entries = sparse
  frame.dense = false
}
function startArray(frame: Frame) {
  if (!Array.isArray(frame.value)) fail('array brand')
  const initial = (frame.value as unknown[]).length
  if (!int(initial, maxArrayLength)) fail('array length or index invalid')
  frame.length = initial
  frame.index = 0
  frame.count = 0
  frame.dense = true
  frame.entries = []
  frame.phase = 1
}
function url(frame: Frame, context: EncodeContext) {
  if (frame.phase === 0) {
    frame.state = readURL(frame.value) as Frame['state']
    frame.child = frame.state.parameters
    frame.phase = 1
    return false
  }
  context.owner(-(frame.input as number) - 6, context.ids.get(frame.value)!)
  frame.row = [9, frame.state.href]
  return true
}
function view(frame: Frame) {
  if (frame.phase === 0) {
    frame.state = readView(frame.value, frame.detail) as Frame['state']
    frame.child = frame.state.buffer
    frame.phase = 1
    return false
  }
  frame.row = [8, frame.detail, frame.input, frame.state.byteOffset, frame.state.length]
  return true
}
export const advances = [record, record, array, array, map, set, leaf, leaf, view, url, leaf, leaf]
