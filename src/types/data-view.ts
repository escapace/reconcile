import { freeze } from './shared/empty'
import { copyDataView } from './shared/binary-native'
import {
  viewDraft,
  viewCapture,
  viewConstruction,
  viewPublication,
  viewImmutable,
} from './shared/binary'

/** Stable global identity owned by the data-view module. */
export const DATA_VIEW_KIND = Symbol.for('@escapace/reconcile/data-view')

const dataViewCapture = /* @__PURE__ */ viewCapture(DATA_VIEW_KIND, copyDataView)
const dataViewConstruction = /* @__PURE__ */ viewConstruction<typeof DATA_VIEW_KIND>(copyDataView)
export const dataViewPublication = /* @__PURE__ */ (() =>
  /* @__PURE__ */ freeze({
    ...dataViewCapture,
    ...dataViewConstruction,
    .../* @__PURE__ */ viewPublication<typeof DATA_VIEW_KIND>(),
  }))()
export const dataViewImmutable = /* @__PURE__ */ viewImmutable<typeof DATA_VIEW_KIND>(copyDataView)
export const dataViewDraft = viewDraft
