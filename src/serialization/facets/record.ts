import { decodeFail as fail, define } from '../common'
import type { Decoder } from '../contracts'
import { resolve } from './slots'
function record(prototype: null | undefined): Decoder {
  return {
    allocate(payload, layout, context) {
      if (payload.length !== context.shapes[layout[1]].length) fail('object shape arity')
      return prototype === null ? (Object.create(null) as object) : {}
    },
    fill(payload, value, layout, context) {
      resolve(payload, layout, 2, context)
      const keys = context.shapes[layout[1]]
      for (let index = 0; index < keys.length; index++)
        define(value as object, keys[index], payload[index])
    },
  }
}
export const ordinaryRecord = /* @__PURE__ */ record(undefined)
export const nullRecord = /* @__PURE__ */ record(null)
