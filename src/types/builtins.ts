import { freeze } from './shared/empty'
import type { SnapshotRegistry, PublicationRegistry, ImmutableRegistry } from '../types'
import { registerTypes, registerRecognition } from './registry'
import * as array from './array'
import * as date from './date'
import * as map from './map'
import * as set from './set'
import * as arrayBuffer from './array-buffer'
import * as dataView from './data-view'
import * as typedArray from './typed-array'
import * as object from './object'

/** Orders native recognition with the plain-object fallback last. */
export const builtinModules = [
  array.arrayType,
  date.dateType,
  map.mapType,
  set.setType,
  arrayBuffer.arrayBufferType,
  dataView.dataViewType,
  typedArray.typedArrayType,
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
  object.OBJECT_KIND,
] as const

/** Freezes one kind-indexed facet table; each registry references only its own facets. */
function table<T>(facets: readonly T[]): Readonly<Record<symbol, T>> {
  return Object.freeze(Object.fromEntries(KINDS.map((kind, index) => [kind, facets[index]])))
}

const recognition = /* @__PURE__ */ registerRecognition(
  [
    array.arrayRecognition,
    date.dateRecognition,
    map.mapRecognition,
    set.setRecognition,
    arrayBuffer.arrayBufferRecognition,
    dataView.dataViewRecognition,
    typedArray.typedArrayRecognition,
    object.objectRecognition,
  ].map((recognition, index) => ({ kind: KINDS[index], recognition })),
)

export const snapshotTypes: SnapshotRegistry = /* @__PURE__ */ (() =>
  freeze({
    ...recognition,
    policies: table([
      array.arraySnapshot,
      date.dateSnapshot,
      map.mapSnapshot,
      set.setSnapshot,
      arrayBuffer.arrayBufferSnapshot,
      dataView.dataViewSnapshot,
      typedArray.typedArraySnapshot,
      object.objectSnapshot,
    ]) as unknown as SnapshotRegistry['policies'],
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
      object.objectPublication,
    ]) as unknown as PublicationRegistry['policies'],
  }))()

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
    object.objectImmutable,
  ] as const
  const specials: Record<symbol, unknown> = {}
  const structural: Record<symbol, unknown> = {}
  for (const [index, facet] of immutable.entries()) {
    freeze(facet)
    if (facet.immutable.tag === 'copy') specials[KINDS[index]] = facet.immutable.operations
    else structural[KINDS[index]] = facet.immutable
  }
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
      object.objectDraft,
    ]) as unknown as ImmutableRegistry['drafts'],
    policies: table(immutable) as unknown as ImmutableRegistry['policies'],
    specials: freeze(specials) as ImmutableRegistry['specials'],
    structural: freeze(structural) as ImmutableRegistry['structural'],
  })
})()
