import { decodeFail as fail, define } from '../common'
import type { Decoder } from '../contracts'
import { resolve } from './slots'
// A record's layout key is its shape id; the shape's keys are read in place from the control
// table, its length preceding the first key.
function record(prototype: null | undefined): Decoder {
  return {
    allocate(payload, layout, context) {
      const keys = context.shapes[context.control[layout + 1] as number]
      if (payload.length !== context.control[keys - 1]) fail('object shape arity')
      return prototype === null ? (Object.create(null) as object) : {}
    },
    fill(payload, value, layout, context) {
      resolve(payload, layout, context)
      const { control } = context
      const keys = context.shapes[control[layout + 1] as number]
      for (let index = 0; index < payload.length; index++)
        define(value as object, control[keys + index] as string, payload[index])
    },
  }
}
export const ordinaryRecord = /* @__PURE__ */ record(undefined)
export const nullRecord = /* @__PURE__ */ record(null)
