import { freeze } from './shared/empty'
import { copyTypedArray } from './shared/binary-native'
import {
  viewDraft,
  viewCapture,
  viewConstruction,
  viewPublication,
  viewImmutable,
} from './shared/binary'

/** Stable global identity owned by the typed-array module. */
export const TYPED_ARRAY_KIND = Symbol.for('@escapace/reconcile/typed-array')

const typedArrayCapture = /* @__PURE__ */ viewCapture(TYPED_ARRAY_KIND, copyTypedArray)
const typedArrayConstruction =
  /* @__PURE__ */ viewConstruction<typeof TYPED_ARRAY_KIND>(copyTypedArray)
export const typedArrayPublication = /* @__PURE__ */ (() =>
  /* @__PURE__ */ freeze({
    ...typedArrayCapture,
    ...typedArrayConstruction,
    .../* @__PURE__ */ viewPublication<typeof TYPED_ARRAY_KIND>(),
  }))()
export const typedArrayImmutable = /* @__PURE__ */ (() => ({
  ...typedArrayConstruction,
  .../* @__PURE__ */ viewImmutable<typeof TYPED_ARRAY_KIND>(copyTypedArray),
}))()
export const typedArrayDraft = viewDraft
