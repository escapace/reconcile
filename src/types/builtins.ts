import { freeze } from './shared/empty'
import type {
  ImmutableRegistry,
  PrototypeRead,
  PublicationRegistry,
  SnapshotRegistry,
} from '../types'
import * as array from './array'
import * as date from './date'
import * as map from './map'
import * as set from './set'
import * as arrayBuffer from './array-buffer'
import * as dataView from './data-view'
import * as typedArray from './typed-array'
import * as temporal from './temporal'
import * as url from './url'
import * as urlSearchParameters from './url-search-parameters'
import * as object from './object'
import { ATOM_KIND } from '../constants'
import { inChain, prototypeOf } from '../object-property'
import { bufferOfView, typedArrayClass, viewElement } from './shared/binary-native'

/** Built-in kinds in recognition order; every facet table below lists facets in this order. */
const KINDS = [
  array.ARRAY_KIND,
  date.DATE_KIND,
  map.MAP_KIND,
  set.SET_KIND,
  arrayBuffer.ARRAY_BUFFER_KIND,
  dataView.DATA_VIEW_KIND,
  typedArray.TYPED_ARRAY_KIND,
  temporal.TEMPORAL_KIND,
  url.URL_KIND,
  urlSearchParameters.URL_SEARCH_PARAMS_KIND,
  object.OBJECT_KIND,
] as const

/** Freezes one kind-indexed facet table; each registry references only its own facets. */
function table<T>(facets: readonly T[]): Readonly<Record<symbol, T>> {
  return Object.freeze(Object.fromEntries(KINDS.map((kind, index) => [kind, facets[index]])))
}

// The plain-object fallback's rank, the last in recognition order.
const FALLBACK_RANK = 10

/**
 * The kind at the first matching rank up to `last`, or undefined; at the fallback rank, the kind.
 *
 * @remarks
 * After the array probe the value's prototype is read once. A value whose prototype is
 * `Object.prototype` or `null` fails every later probe, a view included, and the fallback decides
 * it. Otherwise each constructor probe walks the chain from that prototype, in
 * the ordered scan's order, so the value itself is not read again. Types.RecognitionPlain.
 * recognize_eq_scan proves the result is the ordered scan's.
 */
function builtinFirstMatch(value: object, last: number, read?: PrototypeRead): symbol | undefined {
  if (Array.isArray(value)) return array.ARRAY_KIND
  if (last === 0) return undefined
  const first = prototypeOf(value, read)
  if (first === Object.prototype || first === null)
    return last === FALLBACK_RANK ? object.OBJECT_KIND : undefined
  if (inChain(first, Date)) return date.DATE_KIND
  if (last === 1) return undefined
  if (inChain(first, Map)) return map.MAP_KIND
  if (last === 2) return undefined
  if (inChain(first, Set)) return set.SET_KIND
  if (last === 3) return undefined
  if (inChain(first, ArrayBuffer)) return arrayBuffer.ARRAY_BUFFER_KIND
  if (last === 4) return undefined
  return builtinRemainingMatch(value, first, last)
}

/**
 * Whether the buffer of the view `value` is recognized: an `ArrayBuffer` or `SharedArrayBuffer` of
 * this environment by its prototype chain. A view over any other buffer, such as one from another
 * environment or one whose prototype was replaced, is not recognized either. Reading a view's own
 * buffer observes nothing.
 */
function recognizedBuffer(value: object): boolean {
  const prototype = Object.getPrototypeOf(bufferOfView(value)) as object | null
  return (
    inChain(prototype, ArrayBuffer) ||
    (typeof SharedArrayBuffer === 'function' && inChain(prototype, SharedArrayBuffer))
  )
}

/** Continues the same ordered prefix without allocating a per-value continuation. A typed array
 * holds the typed-array brand and inherits `%TypedArray%.prototype`, so a `DataView` that inherits
 * a typed array's prototype is not one; it needs no walk for `DataView` here, since the `DataView`
 * probe has decided it. */
function builtinRemainingMatch(
  value: object,
  first: object | null,
  last: number,
): symbol | undefined {
  const isDataView = inChain(first, DataView)
  // Undefined without a view brand; otherwise whether the view's buffer is recognized.
  const view = ArrayBuffer.isView(value) ? recognizedBuffer(value) : undefined
  if (isDataView && view !== false) return dataView.DATA_VIEW_KIND
  if (last === 5) return undefined
  if (
    !isDataView &&
    view === true &&
    viewElement(value) !== undefined &&
    inChain(first, typedArrayClass)
  )
    return typedArray.TYPED_ARRAY_KIND
  if (last === 6) return undefined
  if (temporal.temporalInChain(first)) return temporal.TEMPORAL_KIND
  if (last === 7) return undefined
  if (typeof URL !== 'undefined' && inChain(first, URL)) return url.URL_KIND
  if (last === 8) return undefined
  if (
    typeof URL !== 'undefined' &&
    typeof URLSearchParams !== 'undefined' &&
    inChain(first, URLSearchParams)
  )
    return urlSearchParameters.URL_SEARCH_PARAMS_KIND
  if (last === 9) return undefined
  return object.OBJECT_KIND
}

const builtinRecognize = (value: object, read?: PrototypeRead): symbol =>
  builtinFirstMatch(value, FALLBACK_RANK, read)!

const recognition = /* @__PURE__ */ (() => {
  const positions = new Map<symbol, number>(KINDS.map((kind, index) => [kind, index]))
  return {
    recognize: builtinRecognize,
    // Callers ask only about the kinds of their nodes, which are built-in kinds.
    matches: (kind: symbol, value: object): boolean =>
      builtinFirstMatch(value, positions.get(kind)!) === kind,
  }
})()

// `snapshot` copies objects, arrays, Maps, Sets, Dates, buffers and views inline when it walks
// with this registry, so only the kinds it observes through their facets are listed.
export const snapshotTypes: SnapshotRegistry = /* @__PURE__ */ (() =>
  freeze({
    policies: freeze({
      [temporal.TEMPORAL_KIND]: temporal.temporalSnapshot,
      [url.URL_KIND]: url.urlSnapshot,
      [urlSearchParameters.URL_SEARCH_PARAMS_KIND]: urlSearchParameters.urlSearchParametersSnapshot,
    }) as unknown as SnapshotRegistry['policies'],
    recognize: builtinRecognize,
  }))()

export const publicationTypes: PublicationRegistry = /* @__PURE__ */ (() =>
  freeze({
    ...recognition,
    policies: table([
      array.arrayPublication,
      date.datePublication,
      map.mapPublication,
      set.setPublication,
      arrayBuffer.arrayBufferPublication,
      dataView.dataViewPublication,
      typedArray.typedArrayPublication,
      temporal.temporalPublication,
      url.urlPublication,
      urlSearchParameters.urlSearchParametersPublication,
      object.objectPublication,
    ]) as unknown as PublicationRegistry['policies'],
  }))()

const atomLeaf = /* @__PURE__ */ freeze({ someChild: () => false })

export const produceTypes: ImmutableRegistry = /* @__PURE__ */ (() => {
  // Special copies resolve through `specials`, so production needs no snapshot facet.
  const immutable = [
    array.arrayImmutable,
    date.dateImmutable,
    map.mapImmutable,
    set.setImmutable,
    arrayBuffer.arrayBufferImmutable,
    dataView.dataViewImmutable,
    typedArray.typedArrayImmutable,
    temporal.temporalImmutable,
    url.urlImmutable,
    urlSearchParameters.urlSearchParametersImmutable,
    object.objectImmutable,
  ] as const
  const specials: Record<symbol, unknown> = {}
  const structural: Record<symbol, unknown> = {}
  for (let index = 0; index < immutable.length; index += 1) {
    const facet = immutable[index]
    freeze(facet)
    if (facet.immutable.tag === 'copy') specials[KINDS[index]] = facet.immutable.operations
    else structural[KINDS[index]] = facet.immutable
  }
  // An atom is a fixed leaf: identity restoration asks it for children and finds none.
  const policies: Record<symbol, unknown> = { ...table(immutable), [ATOM_KIND]: atomLeaf }
  return freeze({
    ...recognition,
    drafts: table([
      array.arrayDraft,
      date.dateDraft,
      map.mapDraft,
      set.setDraft,
      arrayBuffer.arrayBufferDraft,
      dataView.dataViewDraft,
      typedArray.typedArrayDraft,
      temporal.temporalDraft,
      url.urlDraft,
      urlSearchParameters.urlSearchParametersDraft,
      object.objectDraft,
    ]) as unknown as ImmutableRegistry['drafts'],
    policies: freeze(policies) as unknown as ImmutableRegistry['policies'],
    specials: freeze(specials) as ImmutableRegistry['specials'],
    structural: freeze(structural) as ImmutableRegistry['structural'],
  })
})()
