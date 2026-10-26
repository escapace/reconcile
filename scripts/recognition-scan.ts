import { ARRAY_KIND } from '../src/types/array'
import { ARRAY_BUFFER_KIND } from '../src/types/array-buffer'
import { DATA_VIEW_KIND } from '../src/types/data-view'
import { DATE_KIND } from '../src/types/date'
import { MAP_KIND } from '../src/types/map'
import { OBJECT_KIND } from '../src/types/object'
import { SET_KIND } from '../src/types/set'
import { TEMPORAL_KIND, temporalInChain } from '../src/types/temporal'
import { TYPED_ARRAY_KIND } from '../src/types/typed-array'
import { URL_KIND } from '../src/types/url'
import { URL_SEARCH_PARAMS_KIND } from '../src/types/url-search-parameters'
import { bufferOfView, viewElement } from '../src/types/shared/binary-native'

/** Whether `constructor.prototype` is on the chain of `value`, read from `value` itself as
 * `instanceof` reads it, without a constructor's `Symbol.hasInstance`. */
const inChainOf = (constructor: { readonly prototype: unknown }, value: object): boolean =>
  Object.prototype.isPrototypeOf.call(constructor.prototype, value)

/** Whether `value` is no view, or a view over a buffer of this environment: one whose chain holds
 * `ArrayBuffer.prototype` or `SharedArrayBuffer.prototype`. */
/** `%TypedArray%`, as a probe target: the class every built-in typed array class extends. */
const typedArrayClass = { prototype: Object.getPrototypeOf(Uint8Array.prototype) as object }

const knownView = (value: object): boolean => {
  if (!ArrayBuffer.isView(value)) return true
  const buffer = bufferOfView(value)
  return inChainOf(ArrayBuffer, buffer) || inChainOf(SharedArrayBuffer, buffer)
}

/**
 * The built-in kinds in recognition order, each with its probe; the plain-object fallback is
 * last and has none.
 *
 * @remarks
 * Each probe reads the value again, as the ordered scan of `Types.Recognition` does. Built-in
 * recognition reads it once and must agree with this scan.
 */
const probes: ReadonlyArray<readonly [symbol, (value: object) => boolean]> = [
  [ARRAY_KIND, (value) => Array.isArray(value)],
  [DATE_KIND, (value) => inChainOf(Date, value)],
  [MAP_KIND, (value) => inChainOf(Map, value)],
  [SET_KIND, (value) => inChainOf(Set, value)],
  [ARRAY_BUFFER_KIND, (value) => inChainOf(ArrayBuffer, value)],
  [DATA_VIEW_KIND, (value) => inChainOf(DataView, value) && knownView(value)],
  [
    TYPED_ARRAY_KIND,
    (value) =>
      ArrayBuffer.isView(value) &&
      knownView(value) &&
      viewElement(value) !== undefined &&
      !inChainOf(DataView, value) &&
      inChainOf(typedArrayClass, value),
  ],
  [
    TEMPORAL_KIND,
    (value) => temporalInChain(Object.getPrototypeOf(value) as object | null, undefined),
  ],
  [URL_KIND, (value) => typeof URL !== 'undefined' && inChainOf(URL, value)],
  [
    URL_SEARCH_PARAMS_KIND,
    (value) =>
      typeof URL !== 'undefined' &&
      typeof URLSearchParams !== 'undefined' &&
      inChainOf(URLSearchParams, value),
  ],
]

/** The built-in kinds in recognition order, the plain-object fallback last. */
export const recognitionOrder: readonly symbol[] = [...probes.map(([kind]) => kind), OBJECT_KIND]

/** The kind at the first matching rank up to `last`, or undefined; the fallback rank matches. */
function firstMatch(value: object, last: number): symbol | undefined {
  for (let index = 0; index <= last; index += 1) {
    if (index === probes.length) return OBJECT_KIND
    const [kind, test] = probes[index]
    if (test(value)) return kind
  }
  return undefined
}

/** The ordered scan: a test reference for built-in recognition and known-kind checks. */
export const orderedScan = {
  matches: (kind: symbol, value: object): boolean =>
    firstMatch(value, recognitionOrder.indexOf(kind)) === kind,
  recognize: (value: object): symbol => firstMatch(value, probes.length)!,
}
