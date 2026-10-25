import { EMPTY_FACTS } from '../constants'
import { freeze, independentBindings, same } from './shared/empty'
import type { SpecialPolicy } from '../types'
import { independentDraft } from './shared/empty'
import { noValue } from './shared/empty'
import type {
  CapturePolicy,
  ConstructionPolicy,
  SnapshotPolicy,
  PublicationPolicy,
  ImmutablePolicy,
  Recognition,
} from '../types'
import { defineType } from './registry'
import { bufferEquivalent } from './shared/bytes'
import {
  bufferByteLength,
  bufferMaximum,
  copyBuffer,
  copyChangedBytes,
} from './shared/binary-native'
import { noChildren, noDependencies } from './shared/empty'

/** Stable global identity owned by the array-buffer module. */
export const ARRAY_BUFFER_KIND = Symbol.for('@escapace/reconcile/array-buffer')

const arrayBufferCapture = {
  construction: (layout) => layout.bytes,
  observe(value, begin) {
    begin({ bytes: copyBuffer(value), kind: ARRAY_BUFFER_KIND })
  },
} satisfies CapturePolicy<ArrayBufferLayout>

const arrayBufferConstruction = {
  bindings: independentBindings,
  allocate: (node) => copyBuffer(node.layout.bytes),
} satisfies ConstructionPolicy<ArrayBufferLayout>

export const arrayBufferSnapshot = /* @__PURE__ */ (() =>
  /* @__PURE__ */ freeze({
    ...arrayBufferCapture,
    snapshot(layout, _resolve, writer) {
      writer.initialize(layout, layout.bytes, noValue)
    },
  }))() satisfies SnapshotPolicy<ArrayBufferLayout>

export const arrayBufferPublication = /* @__PURE__ */ (() =>
  /* @__PURE__ */ freeze({
    ...arrayBufferCapture,
    ...arrayBufferConstruction,
    aligned: noValue,
    // A kept buffer takes next's bytes in place, so it must already have next's length and, as a
    // copy would, its resizability and maximum.
    seal: same,
    matches: (node, current) => bufferEquivalent(current as ArrayBuffer, node.layout.bytes),
    requirements: (node, current) =>
      bufferByteLength(current) === bufferByteLength(node.layout.bytes) &&
      bufferMaximum(current) === bufferMaximum(node.layout.bytes)
        ? EMPTY_FACTS
        : undefined,
    // Equal bytes are not written, and readback, which compares the same bytes, would accept them;
    // `compatible` matched the lengths.
    publish(node, current, _resolve, _owner, note) {
      const wrote = copyChangedBytes(current as ArrayBuffer, node.layout.bytes)
      if (note !== undefined) note.unchanged = !wrote
      return true
    },
  }))() satisfies PublicationPolicy<ArrayBufferLayout>

export const arrayBufferImmutable = /* @__PURE__ */ (() => ({
  ...arrayBufferConstruction,
  freshWrite: noValue,
  immutable: /* @__PURE__ */ freeze({
    operations: /* @__PURE__ */ freeze({
      dependencies: noDependencies,
      copy: (value) => copyBuffer(value),
      equivalent: (base, candidate) =>
        bufferEquivalent(base as ArrayBuffer, candidate as ArrayBuffer),
    } satisfies SpecialPolicy),
    tag: 'copy',
  } satisfies ImmutablePolicy<ArrayBufferLayout>['immutable']),
  someChild: noChildren,
}))() satisfies ImmutablePolicy<ArrayBufferLayout>

const arrayBufferPolicy = /* @__PURE__ */ (() => ({
  ...arrayBufferSnapshot,
  ...arrayBufferPublication,
  ...arrayBufferImmutable,
}))()

/** Stores copied bytes used for construction and publication of a captured buffer. */
// fallow-ignore-next-line unused-type -- part of the declared type of builtinModules in builtins.ts
export interface ArrayBufferLayout {
  readonly bytes: ArrayBuffer
  readonly kind: typeof ARRAY_BUFFER_KIND
}

export const arrayBufferDraft = /* @__PURE__ */ independentDraft

const arrayBufferRecognition = /* @__PURE__ */ freeze({
  tag: 'predicate',
  test: (value: object) => value instanceof ArrayBuffer,
}) satisfies Recognition

export const arrayBufferType = /* @__PURE__ */ defineType<ArrayBufferLayout>({
  draft: arrayBufferDraft,
  kind: ARRAY_BUFFER_KIND,
  name: 'array-buffer',
  policy: arrayBufferPolicy,
  recognition: arrayBufferRecognition,
})
