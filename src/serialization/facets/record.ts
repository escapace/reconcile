import { decodeFail as fail, int, define } from '../common'
import type { Decoder } from '../contracts'
function record(kind: number): Decoder {
  return {
    allocate(row, context) {
      const shape = row[1]
      if (!int(shape, context.shapes.length - 1)) fail('shape reference')
      const keys = context.shapes[shape]
      if (!context.checkedShapes.has(shape)) {
        if (!Array.isArray(keys)) fail('shape')
        const seen = new Set<string>()
        for (const key of keys as unknown[]) {
          if (typeof key !== 'string' || seen.has(key)) fail('shape key')
          seen.add(key)
        }
        context.checkedShapes.add(shape)
      }
      if (row.length !== (keys as string[]).length + 2) fail('object shape arity')
      return kind === 1 ? (Object.create(null) as object) : {}
    },
    fill(row, value, context) {
      const keys = context.shapes[row[1] as number] as string[]
      for (let index = 0; index < keys.length; index++)
        define(value as object, keys[index], context.read(row[index + 2]))
    },
  }
}
export const ordinaryRecord = /* @__PURE__ */ record(0)
export const nullRecord = /* @__PURE__ */ record(1)
