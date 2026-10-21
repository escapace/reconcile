import { decodeFail as fail, int } from '../common'
import { checkBytes, decodedSize, decodeBytes } from '../binary'
import {
  dataViewKind,
  decodeTemporal,
  constructView,
  viewConstructors,
  temporalNames,
} from '../native'
import type { DecodeContext, Decoder } from '../contracts'
import { enter } from './slots'
import { charge, chargeParameters, stringWords } from '../size'
import { denseArray, filledArray } from '../../standard-prototypes'
export const date: Decoder = {
  fill: undefined,
  link: undefined,
  allocate(payload, _layout, context) {
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
    // A header and the time value.
    if (context.limited) charge(context, 2)
    return new Date(time ?? NaN)
  },
}
export const buffer: Decoder = {
  fill: undefined,
  link: undefined,
  allocate(payload, _layout, context) {
    if (payload.length !== 1) fail('base64')
    const length = decodedSize(payload[0])
    if (context.limited) charge(context, 1 + Math.ceil(length / 8))
    return (context.measuring ? checkBytes : decodeBytes)(payload[0] as string, length)
  },
}
// A view is [buffer reference, byte offset, length]; Positional.lean typedRef_sound: the
// reference must name a buffer node.
// Each view is charged its own bytes: views over one buffer each expose them.
export const view: Decoder = {
  allocate(payload, layout, context) {
    if (payload.length !== 3 || !int(payload[1]) || !int(payload[2])) fail('view')
    if (context.limited)
      charge(
        context,
        1 + Math.ceil((payload[2] * viewUnit(context.control[layout + 1] as number)) / 8),
      )
  },
  fill(payload, _value, _layout, context) {
    enter(payload[0] as number, context)
  },
  link(payload, layout, context) {
    const storage = typed(payload[0], 7, context) as ArrayBuffer
    const kind = context.control[layout + 1] as number
    const offset = payload[1] as number
    const length = payload[2] as number
    const unit = viewUnit(kind)
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
  link: undefined,
  allocate(payload, _layout, context) {
    if (payload.length !== 1 || typeof payload[0] !== 'string') fail('URL')
    context.urls++
    const value = new URL(payload[0])
    // Charged by the text it holds, which parsing can lengthen.
    if (context.limited) charge(context, 1 + stringWords(value.href.length))
    return value
  },
  fill(_payload, _value, _layout, context, index) {
    enter(context.parameters![index]!, context)
  },
}
export const parameters: Decoder = {
  fill: undefined,
  link: undefined,
  allocate(payload, _layout, context) {
    if (payload.length !== 1 || typeof payload[0] !== 'string') fail('params')
    const value = new URLSearchParams(payload[0])
    if (context.limited) chargeParameters(context, value)
    return value
  },
}
// A URL's own parameters reference their URL; every URL is owned exactly once.
export const ownedParameters: Decoder = {
  fill: undefined,
  allocate(payload) {
    if (payload.length !== 1) fail('params owner')
  },
  link(payload, _layout, context, index) {
    const owner = typed(payload[0], 9, context) as URL
    const parameters = (context.parameters ??= denseArray<number | undefined>(
      context.output.length,
    ))
    if (parameters[payload[0] as number] !== undefined) fail('params owner')
    parameters[payload[0] as number] = index
    context.owned++
    if (context.limited) chargeParameters(context, owner.searchParams)
    return owner.searchParams
  },
}
export const temporal: Decoder = {
  fill: undefined,
  link: undefined,
  allocate(payload, layout, context) {
    const kind = context.control[layout + 1] as number
    if (kind === 7) {
      if (payload.length !== 10 || !payload.every(integer)) fail('duration')
      // A header and ten fields.
      if (context.limited) charge(context, 11)
      return decodeTemporal(kind, payload as number[])
    }
    if (payload.length !== 1 || typeof payload[0] !== 'string') fail('Temporal text')
    const value = decodeTemporal(kind, payload[0])
    // Charged by the text it holds, which may be longer than accepted shorter input.
    if (context.limited)
      charge(context, 1 + stringWords((value as { toString: () => string }).toString().length))
    return value
  },
}
// Shared scalar nodes: undefined, NaN, Infinity, -Infinity and -0 by tag, then bigints.
const scalarValues = [undefined, NaN, Infinity, -Infinity, -0]
export const scalar: Decoder = {
  fill: undefined,
  link: undefined,
  allocate(payload, layout, context) {
    if (payload.length !== 0) fail('scalar')
    return scalarValues[(context.control[layout] as number) - 13]
  },
}
// Size.lean encodeInt_decodeInt: canonical text (`0x`, lowercase digits, no leading zero, no
// -0x0) has one value, so each bigint has one encoding. BigInt reads `0x` text but not `-0x`.
// A bigint is a primitive, charged at every occurrence: sixteen hexadecimal digits per word.
export const bigint: Decoder = {
  fill: undefined,
  link: undefined,
  allocate(payload, _layout, context, index) {
    const text = payload[0]
    if (
      payload.length !== 1 ||
      typeof text !== 'string' ||
      /^(?:0x0|-?0x[1-9a-f][\da-f]*)$/.exec(text) === null
    )
      fail('bigint')
    const negative = text.charCodeAt(0) === 45
    if (context.limited)
      (context.weights ??= filledArray(context.output.length, 0))[index] = Math.ceil(
        (text.length - (negative ? 3 : 2)) / 16,
      )
    return negative ? -BigInt(text.slice(1)) : BigInt(text)
  },
}

export function validViewKind(kind: unknown): kind is number {
  return int(kind, dataViewKind) && (kind === dataViewKind || viewConstructors[kind] !== undefined)
}
function integer(value: unknown): boolean {
  return Number.isInteger(value) && !Object.is(value, -0)
}
function typed(reference: unknown, tag: number, context: DecodeContext): unknown {
  if (
    !int(reference, context.output.length - 1) ||
    context.control[context.nodeLayouts[reference]] !== tag
  )
    fail('typed reference')
  return context.output[reference]
}
function viewUnit(kind: number): number {
  return kind === dataViewKind ? 1 : viewConstructors[kind]!.BYTES_PER_ELEMENT
}
// Temporal kinds index temporalNames. The annotated call lets bundlers drop an unused count.
export const temporalKinds = /* @__PURE__ */ (() => temporalNames.length)()
