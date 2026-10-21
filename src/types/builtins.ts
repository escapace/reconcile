import { freeze } from './shared/empty'
import type { SnapshotRegistry, PublicationRegistry, ImmutableRegistry } from '../types'
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

/** Full recognition needs no bounded-prefix checks; it retains the same native trace. */
function builtinRecognize(value: object): symbol {
  if (array.arrayRecognition.test(value)) return array.ARRAY_KIND
  if (date.dateRecognition.test(value)) return date.DATE_KIND
  if (map.mapRecognition.test(value)) return map.MAP_KIND
  if (set.setRecognition.test(value)) return set.SET_KIND
  if (arrayBuffer.arrayBufferRecognition.test(value)) return arrayBuffer.ARRAY_BUFFER_KIND
  if (dataView.dataViewRecognition.test(value)) return dataView.DATA_VIEW_KIND
  if (typedArray.typedArrayRecognition.test(value)) return typedArray.TYPED_ARRAY_KIND
  if (temporal.temporalRecognition.test(value)) return temporal.TEMPORAL_KIND
  if (url.urlRecognition.test(value)) return url.URL_KIND
  if (urlSearchParameters.urlSearchParametersRecognition.test(value))
    return urlSearchParameters.URL_SEARCH_PARAMS_KIND
  return object.OBJECT_KIND
}

/** Static call sites preserve the generic recognizer's exact predicate prefix and exceptions.
 * Types.Recognition.builtinTrace_eq_scanTrace proves the finite unrolling.
 */
function builtinFirstMatch(value: object, last: number): symbol | undefined {
  if (array.arrayRecognition.test(value)) return array.ARRAY_KIND
  if (last === 0) return undefined
  if (date.dateRecognition.test(value)) return date.DATE_KIND
  if (last === 1) return undefined
  if (map.mapRecognition.test(value)) return map.MAP_KIND
  if (last === 2) return undefined
  if (set.setRecognition.test(value)) return set.SET_KIND
  if (last === 3) return undefined
  if (arrayBuffer.arrayBufferRecognition.test(value)) return arrayBuffer.ARRAY_BUFFER_KIND
  if (last === 4) return undefined
  return builtinRemainingMatch(value, last)
}

/** Continues the same ordered prefix without allocating a per-value continuation. */
function builtinRemainingMatch(value: object, last: number): symbol | undefined {
  if (dataView.dataViewRecognition.test(value)) return dataView.DATA_VIEW_KIND
  if (last === 5) return undefined
  if (typedArray.typedArrayRecognition.test(value)) return typedArray.TYPED_ARRAY_KIND
  if (last === 6) return undefined
  if (temporal.temporalRecognition.test(value)) return temporal.TEMPORAL_KIND
  if (last === 7) return undefined
  if (url.urlRecognition.test(value)) return url.URL_KIND
  if (last === 8) return undefined
  if (urlSearchParameters.urlSearchParametersRecognition.test(value))
    return urlSearchParameters.URL_SEARCH_PARAMS_KIND
  if (last === 9) return undefined
  return object.OBJECT_KIND
}

const recognition = /* @__PURE__ */ (() => {
  const positions = new Map<symbol, number>(KINDS.map((kind, index) => [kind, index]))
  return {
    recognize: builtinRecognize,
    matches(kind: symbol, value: object): boolean {
      const last = positions.get(kind)
      return (
        last !== undefined &&
        (last === KINDS.length - 1 ? builtinRecognize(value) : builtinFirstMatch(value, last)) ===
          kind
      )
    },
  }
})()

export const snapshotTypes: SnapshotRegistry = /* @__PURE__ */ (() =>
  freeze({
    policies: table([
      array.arraySnapshot,
      date.dateSnapshot,
      map.mapSnapshot,
      set.setSnapshot,
      arrayBuffer.arrayBufferSnapshot,
      dataView.dataViewSnapshot,
      typedArray.typedArraySnapshot,
      temporal.temporalSnapshot,
      url.urlSnapshot,
      urlSearchParameters.urlSearchParametersSnapshot,
      object.objectSnapshot,
    ]) as unknown as SnapshotRegistry['policies'],
    recognize: builtinRecognize,
  }))()

export const publicationTypes: PublicationRegistry = /* @__PURE__ */ (() =>
  freeze({
    ...recognition,
    exposures: table([
      array.arrayExposure,
      date.dateExposure,
      map.mapExposure,
      set.setExposure,
      arrayBuffer.arrayBufferExposure,
      dataView.dataViewExposure,
      typedArray.typedArrayExposure,
      temporal.temporalExposure,
      url.urlExposure,
      urlSearchParameters.urlSearchParametersExposure,
      object.objectExposure,
    ]),
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
