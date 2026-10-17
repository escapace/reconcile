import { decodeFail as fail } from '../common'
import type { Decoder } from '../contracts'
import { resolve } from './slots'
// Collection.lean: decode every occurrence, then fold with native insertion semantics.
export const map: Decoder = {
  allocate(payload) {
    if (payload.length % 2 !== 0) fail('map shape')
    return new Map<unknown, unknown>()
  },
  fill(payload, value, layout, context) {
    resolve(payload, layout, context)
    const target = value as Map<unknown, unknown>
    for (let index = 0; index < payload.length; index += 2)
      target.set(payload[index], payload[index + 1])
  },
}
export const set: Decoder = {
  allocate() {
    return new Set<unknown>()
  },
  fill(payload, value, layout, context) {
    resolve(payload, layout, context)
    const target = value as Set<unknown>
    for (let index = 0; index < payload.length; index++) target.add(payload[index])
  },
}
