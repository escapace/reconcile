import { decodeFail as fail } from '../common'
import type { Decoder } from '../contracts'
import { resolve } from './slots'
import { charge } from '../size'
// Collection.lean: decode every occurrence, then fold with native insertion semantics.
// A header and a slot per key, value or member. Repeated keys fold into fewer entries, kept from
// among those charged, so the charge is at least the decoded size (Size.lean foldMap_length_le,
// firstOrder_length_le).
export const map: Decoder = {
  link: undefined,
  allocate(payload, _layout, context) {
    if (payload.length % 2 !== 0) fail('map shape')
    if (context.limited) charge(context, 1 + payload.length)
    return context.measuring ? undefined : new Map<unknown, unknown>()
  },
  fill(payload, value, layout, context) {
    resolve(payload, layout, context)
    if (context.measuring) return
    const target = value as Map<unknown, unknown>
    for (let index = 0; index < payload.length; index += 2)
      target.set(payload[index], payload[index + 1])
  },
}
export const set: Decoder = {
  link: undefined,
  allocate(payload, _layout, context) {
    if (context.limited) charge(context, 1 + payload.length)
    return context.measuring ? undefined : new Set<unknown>()
  },
  fill(payload, value, layout, context) {
    resolve(payload, layout, context)
    if (context.measuring) return
    const target = value as Set<unknown>
    for (let index = 0; index < payload.length; index++) target.add(payload[index])
  },
}
