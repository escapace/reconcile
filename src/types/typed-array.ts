import { freeze } from './shared/empty'
import { ARRAY_BUFFER_KIND } from './array-buffer'
import { copyTypedArray } from './shared/binary-native'
import { defineType } from './registry'
import {
  viewDraft,
  viewCapture,
  viewConstruction,
  viewSnapshot,
  viewPublication,
  viewImmutable,
} from './shared/binary'

/** Stable global identity owned by the typed-array module. */
export const TYPED_ARRAY_KIND = Symbol.for('@escapace/reconcile/typed-array')

const typedArrayCapture = /* @__PURE__ */ viewCapture(TYPED_ARRAY_KIND, copyTypedArray)
const typedArrayConstruction =
  /* @__PURE__ */ viewConstruction<typeof TYPED_ARRAY_KIND>(copyTypedArray)
const typedArraySnapshot = /* @__PURE__ */ (() =>
  /* @__PURE__ */ freeze({
    ...typedArrayCapture,
    .../* @__PURE__ */ viewSnapshot<typeof TYPED_ARRAY_KIND>(),
  }))()
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
const typedArrayRecognition = /* @__PURE__ */ freeze({
  tag: 'predicate',
  test: (value: object) => ArrayBuffer.isView(value) && !(value instanceof DataView),
} as const)
const typedArrayPolicy = /* @__PURE__ */ (() => ({
  ...typedArraySnapshot,
  ...typedArrayPublication,
  ...typedArrayImmutable,
}))()

/** Stores a captured typed-array sample retaining its constructor and view bounds. */
// fallow-ignore-next-line unused-type -- part of the declared type of builtinModules in builtins.ts
export interface TypedArrayLayout {
  readonly kind: typeof TYPED_ARRAY_KIND
  readonly sample: ArrayBufferView
}

export const typedArrayType = /* @__PURE__ */ defineType<TypedArrayLayout>({
  draft: typedArrayDraft,
  kind: TYPED_ARRAY_KIND,
  name: 'typed-array',
  policy: typedArrayPolicy,
  recognition: typedArrayRecognition,
  requires: [ARRAY_BUFFER_KIND],
})
