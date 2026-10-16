import { decodeFail as fail } from '../common'
import type { Decoder } from '../contracts'
export const map: Decoder = {
  allocate(row) {
    if (row.length % 2 !== 1) fail('map shape')
    return new Map<unknown, unknown>()
  },
  fill(row, value, context) {
    const target = value as Map<unknown, unknown>
    for (let index = 1; index < row.length; index += 2) {
      const key = context.read(row[index])
      if (target.has(key)) fail('duplicate map key')
      target.set(key, context.read(row[index + 1]))
    }
  },
}
export const set: Decoder = {
  allocate() {
    return new Set<unknown>()
  },
  fill(row, value, context) {
    const target = value as Set<unknown>
    for (let index = 1; index < row.length; index++) {
      const child = context.read(row[index])
      if (target.has(child)) fail('duplicate set member')
      target.add(child)
    }
  },
}
