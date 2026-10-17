import { decodeFail as fail, int } from '../common'
import { decodedSize, decodeBytes } from '../binary'
import {
  dataViewKind,
  decodeTemporal,
  constructView,
  viewConstructors,
  temporalNames,
} from '../native'
import type { DecodeContext, Decoder } from '../contracts'
import { enter } from './slots'
export const date: Decoder = {
  allocate(payload) {
    const time = payload[0]
    if (
      payload.length !== 1 ||
      (time !== null &&
        (typeof time !== 'number' ||
          !Number.isInteger(time) ||
          !(Math.abs(time) <= 8.64e15) ||
          Object.is(time, -0)))
    )
      fail('date')
    return new Date(time ?? NaN)
  },
}
export const buffer: Decoder = {
  allocate(payload) {
    if (payload.length !== 1) fail('base64')
    const length = decodedSize(payload[0])
    return decodeBytes(payload[0] as string, length)
  },
}
// A view is [buffer reference, byte offset, length]; Positional.lean typedRef_sound: the
// reference must name a buffer node.
export const view: Decoder = {
  allocate(payload) {
    if (payload.length !== 3 || !int(payload[1]) || !int(payload[2])) fail('view')
  },
  fill(payload, _value, _layout, context) {
    enter(payload[0] as number, context)
  },
  link(payload, layout, context) {
    const storage = typed(payload[0], 7, context) as ArrayBuffer
    const kind = layout[1]
    const offset = payload[1] as number
    const length = payload[2] as number
    const unit = kind === dataViewKind ? 1 : viewConstructors[kind]!.BYTES_PER_ELEMENT
    if (
      offset % unit !== 0 ||
      offset > storage.byteLength ||
      length > Math.floor((storage.byteLength - offset) / unit)
    )
      fail('view bounds')
    return constructView(kind, storage, offset, length)
  },
}
export const url: Decoder = {
  allocate(payload, _layout, context) {
    if (payload.length !== 1 || typeof payload[0] !== 'string') fail('URL')
    context.urls++
    return new URL(payload[0])
  },
  fill(_payload, _value, _layout, context, index) {
    enter(context.parameters![index], context)
  },
}
export const parameters: Decoder = {
  allocate(payload) {
    if (payload.length !== 1 || typeof payload[0] !== 'string') fail('params')
    return new URLSearchParams(payload[0])
  },
}
// A URL's own parameters reference their URL; every URL is owned exactly once.
export const ownedParameters: Decoder = {
  allocate(payload) {
    if (payload.length !== 1) fail('params owner')
  },
  link(payload, _layout, context, index) {
    const owner = typed(payload[0], 9, context) as URL
    const parameters = (context.parameters ??= [])
    if (parameters[payload[0] as number] !== undefined) fail('params owner')
    parameters[payload[0] as number] = index
    context.owned++
    return owner.searchParams
  },
}
export const temporal: Decoder = {
  allocate(payload, layout) {
    const kind = layout[1]
    if (kind === 7) {
      if (payload.length !== 10 || !payload.every(integer)) fail('duration')
      return decodeTemporal(kind, payload as number[])
    }
    if (payload.length !== 1 || typeof payload[0] !== 'string') fail('Temporal text')
    return decodeTemporal(kind, payload[0])
  },
}
// Shared scalar nodes occur once each; their tags follow 13 in this order.
const scalarValues = [undefined, NaN, Infinity, -Infinity, -0]
export const scalar: Decoder = {
  allocate(payload, layout, context) {
    const bit = 1 << (layout[0] - 13)
    if (payload.length !== 0 || (context.scalars & bit) !== 0) fail('scalar')
    context.scalars |= bit
    return scalarValues[layout[0] - 13]
  },
}
export const bigint: Decoder = {
  allocate(payload, _layout, context) {
    const text = payload[0]
    const seen = (context.bigints ??= new Set())
    if (
      payload.length !== 1 ||
      typeof text !== 'string' ||
      /^(?:0|-?[1-9]\d*)$/.exec(text) === null ||
      seen.has(text)
    )
      fail('bigint')
    seen.add(text)
    return BigInt(text)
  },
}

export function validViewKind(kind: unknown): kind is number {
  return int(kind, dataViewKind) && (kind === dataViewKind || viewConstructors[kind] !== undefined)
}
function integer(value: unknown): boolean {
  return Number.isInteger(value) && !Object.is(value, -0)
}
function typed(reference: unknown, tag: number, context: DecodeContext): unknown {
  if (!int(reference, context.output.length - 1) || context.nodeLayouts[reference][0] !== tag)
    fail('typed reference')
  return context.output[reference]
}
// Temporal kinds index temporalNames.
export const temporalKinds = temporalNames.length
