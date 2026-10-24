import { freeze } from './shared/empty'
import { ARRAY_BUFFER_KIND } from './array-buffer'
import { copyDataView } from './shared/binary-native'
import { defineType } from './registry'
import {
  viewDraft,
  viewCapture,
  viewConstruction,
  viewSnapshot,
  viewPublication,
  viewImmutable,
} from './shared/binary'

/** Stable global identity owned by the data-view module. */
export const DATA_VIEW_KIND = Symbol.for('@escapace/reconcile/data-view')

const dataViewCapture = /* @__PURE__ */ viewCapture(DATA_VIEW_KIND, copyDataView)
const dataViewConstruction = /* @__PURE__ */ viewConstruction<typeof DATA_VIEW_KIND>(copyDataView)
export const dataViewSnapshot = /* @__PURE__ */ (() =>
  /* @__PURE__ */ freeze({
    ...dataViewCapture,
    .../* @__PURE__ */ viewSnapshot<typeof DATA_VIEW_KIND>(),
  }))()
export const dataViewPublication = /* @__PURE__ */ (() =>
  /* @__PURE__ */ freeze({
    ...dataViewCapture,
    ...dataViewConstruction,
    .../* @__PURE__ */ viewPublication<typeof DATA_VIEW_KIND>(),
  }))()
export const dataViewImmutable = /* @__PURE__ */ (() => ({
  ...dataViewConstruction,
  .../* @__PURE__ */ viewImmutable<typeof DATA_VIEW_KIND>(copyDataView),
}))()
export const dataViewDraft = viewDraft
const dataViewRecognition = /* @__PURE__ */ freeze({
  tag: 'predicate',
  test: (value: object) => value instanceof DataView,
} as const)
const dataViewPolicy = /* @__PURE__ */ (() => ({
  ...dataViewSnapshot,
  ...dataViewPublication,
  ...dataViewImmutable,
}))()

/** Stores a captured view sample whose backing buffer is an explicit graph edge. */
// fallow-ignore-next-line unused-type -- part of the declared type of builtinModules in builtins.ts
export interface DataViewLayout {
  readonly kind: typeof DATA_VIEW_KIND
  readonly sample: ArrayBufferView
}

export const dataViewType = /* @__PURE__ */ defineType<DataViewLayout>({
  draft: dataViewDraft,
  kind: DATA_VIEW_KIND,
  name: 'data-view',
  policy: dataViewPolicy,
  recognition: dataViewRecognition,
  requires: [ARRAY_BUFFER_KIND],
})
