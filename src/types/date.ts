import { freeze, independentBindings, same, yes } from './shared/empty'
import type { SpecialPolicy } from '../types'
import { ordinaryExposure, independentDraft } from './shared/empty'
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
import { emptyEdges, noChildren, noDependencies } from './shared/empty'

/** Stable global identity owned by the date module. */
export const DATE_KIND = Symbol.for('@escapace/reconcile/date')

const dateCapture = {
  construction: noValue,
  observe(value, begin) {
    begin({ kind: DATE_KIND, time: (value as Date).getTime() })
  },
} satisfies CapturePolicy<DateLayout>

const dateConstruction = {
  bindings: independentBindings,
  allocate: (node) => new Date(node.layout.time),
} satisfies ConstructionPolicy<DateLayout>

export const dateSnapshot = /* @__PURE__ */ (() =>
  /* @__PURE__ */ freeze({
    ...dateCapture,
    snapshot(layout, _resolve, writer) {
      writer.initialize(layout, new Date(layout.time), noValue)
    },
  }))() satisfies SnapshotPolicy<DateLayout>

export const datePublication = /* @__PURE__ */ (() =>
  /* @__PURE__ */ freeze({
    ...dateCapture,
    ...dateConstruction,
    aligned: noValue,
    compatible: yes,
    requirements: emptyEdges,
    seal: same,
    matches: (node, current) => Object.is((current as Date).getTime(), node.layout.time),
    publish(node, current) {
      ;(current as Date).setTime(node.layout.time)
      return true
    },
  }))() satisfies PublicationPolicy<DateLayout>

export const dateImmutable = /* @__PURE__ */ (() => ({
  ...dateConstruction,
  freshWrite: noValue,
  immutable: /* @__PURE__ */ freeze({
    operations: /* @__PURE__ */ freeze({
      dependencies: noDependencies,
      copy: (value) => new Date((value as Date).getTime()),
      equivalent: (base, candidate) =>
        Object.is((base as Date).getTime(), (candidate as Date).getTime()),
    } satisfies SpecialPolicy),
    tag: 'copy',
  } satisfies ImmutablePolicy<DateLayout>['immutable']),
  someChild: noChildren,
}))() satisfies ImmutablePolicy<DateLayout>

const datePolicy = /* @__PURE__ */ (() => ({
  ...dateSnapshot,
  ...datePublication,
  ...dateImmutable,
}))()

/** Stores the captured native timestamp, including an invalid-date NaN. */
export interface DateLayout {
  readonly kind: typeof DATE_KIND
  readonly time: number
}

export const dateDraft = independentDraft

export const dateExposure = ordinaryExposure

export const dateRecognition = /* @__PURE__ */ freeze({
  tag: 'predicate',
  test: (value: object) => value instanceof Date,
}) satisfies Recognition

export const dateType = /* @__PURE__ */ defineType<DateLayout>({
  draft: dateDraft,
  exposure: dateExposure,
  kind: DATE_KIND,
  name: 'date',
  policy: datePolicy,
  recognition: dateRecognition,
})
