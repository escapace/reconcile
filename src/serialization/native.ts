import {
  nativeURLHref,
  nativeURLSearchParameters,
  nativeParametersText,
} from '../types/shared/url-carrier'
import { encodeFail, decodeFail } from './common'
import { globalTemporal, temporalFrom } from '../standard-prototypes'
import {
  bufferByteLength,
  bufferResizable,
  dataBuffer,
  dataLength,
  dataOffset,
  getter,
  typedBuffer,
  typedLength,
  typedOffset,
  viewConstructors,
} from '../types/shared/binary-native'

interface TemporalConstructor {
  new (...arguments_: Array<number | string>): TemporalValue
  prototype: TemporalValue
  from: (value: unknown) => TemporalValue
}
interface TemporalValue {
  toString: (options?: { calendarName: string }) => string
}
// View kinds index viewConstructors; DataView follows them.
export const dataViewKind = 12
export const temporalNames = /* @__PURE__ */ (() =>
  Object.freeze([
    'Instant',
    'PlainDate',
    'PlainTime',
    'PlainDateTime',
    'PlainYearMonth',
    'PlainMonthDay',
    'ZonedDateTime',
    'Duration',
  ]))()
const durationFields = [
  'years',
  'months',
  'weeks',
  'days',
  'hours',
  'minutes',
  'seconds',
  'milliseconds',
  'microseconds',
  'nanoseconds',
]
// eslint-disable-next-line typescript/unbound-method -- The captured intrinsic is called with its source receiver.
const dateTime = /* @__PURE__ */ (() => Date.prototype.getTime)()
export function constructView(
  kind: number,
  buffer: ArrayBuffer,
  offset: number,
  length: number,
): ArrayBufferView {
  if (kind === dataViewKind) return new DataView(buffer, offset, length)
  const Constructor = viewConstructors[kind]
  if (Constructor === undefined) decodeFail('view kind')
  return new Constructor(buffer, offset, length)
}
export function decodeTemporal(kind: number, payload: string | number[]): object {
  const Constructor = temporalConstructor(kind)
  if (kind === 7) return new Constructor(...(payload as number[]))
  if (kind === 4 || kind === 5) return decodeReferenceDate(Constructor, kind, payload as string)

  return Constructor.from(payload)
}
export function nativeKind(
  value: object,
  prototype: object | null = Object.getPrototypeOf(value) as object | null,
): { detail: number | undefined; tag: number } | undefined {
  if (prototype === Date.prototype) return { detail: undefined, tag: 6 }
  if (prototype === ArrayBuffer.prototype) return { detail: undefined, tag: 7 }
  if (prototype === DataView.prototype) return { detail: dataViewKind, tag: 8 }
  for (let kind = 0; kind < viewConstructors.length; kind++) {
    const Constructor = viewConstructors[kind]
    if (Constructor?.prototype === prototype) return { detail: kind, tag: 8 }
  }
  if (typeof URL === 'function' && prototype === URL.prototype) return { detail: undefined, tag: 9 }
  if (typeof URLSearchParams === 'function' && prototype === URLSearchParams.prototype)
    return { detail: undefined, tag: 10 }
  return temporalKind(prototype)
}
export function readBuffer(value: object): { buffer: ArrayBuffer; byteLength: number } {
  const byteLength = bufferByteLength(value)
  if (bufferResizable !== undefined && Reflect.apply(bufferResizable, value, []) === true)
    encodeFail('resizable buffer')
  return { buffer: value as ArrayBuffer, byteLength }
}
export function readDate(value: object): number {
  return Reflect.apply(dateTime, value, [])
}
export function readParameters(value: object): string {
  return nativeParametersText(value as URLSearchParams)
}
export function readTemporal(
  value: object,
  kind?: number,
): { kind: number; payload: string | number[] } {
  const index = kind!
  // Encoding fails as stringify does, so the decoder's error stays out of stringify bundles.
  const constructor = temporalNamespace()?.[temporalNames[index]]
  if (typeof constructor !== 'function') encodeFail('Temporal unavailable')
  const copy = temporalFrom(constructor, temporalNames[index], value)
  if (index === 7)
    return {
      kind: index,
      payload: durationFields.map(
        (field) => getter(constructor.prototype, field)!.call(copy) as number,
      ),
    }
  const options = index === 4 || index === 5 ? { calendarName: 'always' } : undefined
  return { kind: index, payload: constructor.prototype.toString.call(copy, options) }
}
export function readURL(value: object): { href: string; parameters: URLSearchParams } {
  return { href: nativeURLHref(value as URL), parameters: nativeURLSearchParameters(value as URL) }
}
export function readView(
  value: object,
  kind?: number,
): { buffer: ArrayBuffer; byteOffset: number; length: number } {
  if (kind === dataViewKind)
    return {
      buffer: Reflect.apply(dataBuffer, value, []) as ArrayBuffer,
      byteOffset: Reflect.apply(dataOffset, value, []) as number,
      length: Reflect.apply(dataLength, value, []) as number,
    }
  return {
    buffer: Reflect.apply(typedBuffer, value, []) as ArrayBuffer,
    byteOffset: Reflect.apply(typedOffset, value, []) as number,
    length: Reflect.apply(typedLength, value, []) as number,
  }
}
function decodeReferenceDate(
  Constructor: TemporalConstructor,
  kind: number,
  payload: string,
): object {
  const reference = /^([+-]\d{6}|\d{4})-(\d{2})-(\d{2})\[u-ca=([^\]]+)\]$/.exec(payload)
  if (reference === null) decodeFail('Temporal reference date')
  const year = reference[1]
  const month = reference[2]
  const day = reference[3]
  const calendar = reference[4]
  return kind === 5
    ? new Constructor(Number(month), Number(day), calendar, Number(year))
    : new Constructor(Number(year), Number(month), calendar, Number(day))
}
function temporalConstructor(kind: number): TemporalConstructor {
  const constructor = temporalNamespace()?.[temporalNames[kind]]
  if (typeof constructor !== 'function') decodeFail('Temporal unavailable')
  return constructor
}
function temporalKind(prototype: object | null): { detail: number; tag: number } | undefined {
  const temporal = temporalNamespace()
  if (temporal != null)
    for (let kind = 0; kind < temporalNames.length; kind++) {
      const constructor = temporal[temporalNames[kind]]
      if (typeof constructor === 'function' && prototype === constructor.prototype)
        return { detail: kind, tag: 12 }
    }
  return undefined
}
function temporalNamespace(): Partial<Record<string, TemporalConstructor>> | undefined {
  return globalTemporal() as Partial<Record<string, TemporalConstructor>> | undefined
}
