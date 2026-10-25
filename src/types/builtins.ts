import { freeze } from './shared/empty'
import type {
  ImmutableRegistry,
  PrototypeRead,
  PublicationRegistry,
  SnapshotRegistry,
} from '../types'
import { registerTypes } from './registry'
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

/** Orders native recognition with the plain-object fallback last. */
export const builtinModules = [
  array.arrayType,
  date.dateType,
  map.mapType,
  set.setType,
  arrayBuffer.arrayBufferType,
  dataView.dataViewType,
  typedArray.typedArrayType,
  temporal.temporalType,
  url.urlType,
  urlSearchParameters.urlSearchParametersType,
  object.objectType,
] as const
export const builtinTypes = /* @__PURE__ */ registerTypes(builtinModules)

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
 * `Object.prototype` or `null` and that holds no view brand fails every later probe, and the
 * fallback decides it. Otherwise each `instanceof` probe runs from that prototype, in the generic
 * recognizer's order, so the value itself is not read again. Types.RecognitionPlain.
 * recognize_eq_scan proves the result is the ordered scan's.
 */
function builtinFirstMatch(value: object, last: number, read?: PrototypeRead): symbol | undefined {
  if (array.arrayRecognition.test(value)) return array.ARRAY_KIND
  if (last === 0) return undefined
  const first = prototypeOf(value, read)
  if ((first === Object.prototype || first === null) && !ArrayBuffer.isView(value))
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

/** Continues the same ordered prefix without allocating a per-value continuation. A typed array
 * is the brand check alone here, since the `DataView` probe has failed. */
function builtinRemainingMatch(
  value: object,
  first: object | null,
  last: number,
): symbol | undefined {
  if (inChain(first, DataView)) return dataView.DATA_VIEW_KIND
  if (last === 5) return undefined
  if (ArrayBuffer.isView(value)) return typedArray.TYPED_ARRAY_KIND
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
    matches(kind: symbol, value: object): boolean {
      const last = positions.get(kind)
      return last !== undefined && builtinFirstMatch(value, last) === kind
    },
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
