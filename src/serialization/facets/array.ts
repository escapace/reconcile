import { decodeFail as fail, int, maxArrayLength } from '../common'
import type { Decoder } from '../contracts'
import { resolve, runEnd } from './slots'
import { charge } from '../size'
// JSON.parse defines each element with CreateDataProperty, so a dense payload already is the
// decoded array; only its reference slots are written.
export const denseArray: Decoder = {
  link: undefined,
  allocate(payload, _layout, context) {
    if (context.limited) charge(context, 1 + payload.length)
    return payload
  },
  fill(payload, _value, layout, context) {
    resolve(payload, layout, context)
  },
}
// A sparse payload is [length, presence runs, values]. A mostly present array is allocated at
// its length; a mostly absent one grows from empty as its elements are written in ascending
// order, so storage follows the present elements. Once the length is set the two arrays are
// equal and no written element is lost (Positional.lean sparse_grow_eq_preallocate,
// sparse_resize_keeps).
export const sparseArray: Decoder = {
  link: undefined,
  allocate(payload, _layout, context) {
    if (
      payload.length !== 3 ||
      !int(payload[0], maxArrayLength) ||
      !Array.isArray(payload[1]) ||
      payload[1].length === 0 ||
      !Array.isArray(payload[2])
    )
      fail('sparse array')
    // Every index is a slot, holes included, charged before any storage is allocated.
    if (context.limited) charge(context, 1 + payload[0])
    return (payload[2] as unknown[]).length * 2 >= payload[0] ? new Array<unknown>(payload[0]) : []
  },
  fill(payload, value, layout, context) {
    const values = payload[2] as unknown[]
    resolve(values, layout, context)
    // Placing checks the presence runs and the number of values, so measuring places too, into
    // the new array only.
    place(value as unknown[], payload[0] as number, payload[1] as unknown[], values)
  },
}
// Positional.lean sparse_canonical: presence runs alternate present and hole, present first,
// over the whole length, with the slot runs' rules. A listed run guarantees a hole
// (runsOf_nil_iff), so a dense array has one encoding.
function copy(array: unknown[], position: number, end: number, values: unknown[], next: number) {
  if (next + end - position > values.length) fail('sparse values')
  for (; position < end; position++) array[position] = values[next++]
  return next
}
function place(array: unknown[], length: number, presence: unknown[], values: unknown[]) {
  let position = 0
  let next = 0
  for (let run = 0; run <= presence.length; run++) {
    const end = runEnd(presence, 0, presence.length, run, position, length)
    if (run % 2 === 0) next = copy(array, position, end, values, next)
    position = end
  }
  if (next !== values.length) fail('sparse values')
  array.length = length
}
