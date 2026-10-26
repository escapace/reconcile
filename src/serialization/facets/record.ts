import { decodeFail as fail, define } from '../common'
import type { Decoder } from '../contracts'
import { resolve } from './slots'
import { charge } from '../size'
// A record's layout key is its shape id; the shape's keys are read in place from the control
// table, its length preceding the first key.
function record(prototype: null | undefined): Decoder {
  return {
    link: undefined,
    allocate(payload, layout, context) {
      const shape = context.control[layout + 1] as number
      if (payload.length !== context.control[context.shapes[shape] - 1]) fail('object shape arity')
      // A header, a key slot and a value slot per property, and every key's payload.
      if (context.limited) charge(context, 1 + 2 * payload.length + context.shapeWords[shape])
      if (context.measuring) return undefined
      return prototype === null ? (Object.create(null) as object) : {}
    },
    fill(payload, value, layout, context) {
      resolve(payload, layout, context)
      if (context.measuring) return
      const { control } = context
      const shape = control[layout + 1] as number
      const keys = context.shapes[shape]
      // A key `Object.prototype` lacks is assigned, which reaches nothing; `define` decides each
      // key of a shape that holds one.
      if (context.shapeInherits[shape])
        for (let index = 0; index < payload.length; index++)
          define(value as object, control[keys + index] as string, payload[index])
      else
        for (let index = 0; index < payload.length; index++)
          (value as Record<string, unknown>)[control[keys + index] as string] = payload[index]
    },
  }
}
export const ordinaryRecord = /* @__PURE__ */ record(undefined)
export const nullRecord = /* @__PURE__ */ record(null)
