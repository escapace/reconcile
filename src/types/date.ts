import { adoptPrototype } from './shared/prototype'
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
    const time = (value as Date).getTime()
    begin({ kind: DATE_KIND, prototype: Object.getPrototypeOf(value) as object | null, time })
  },
} satisfies CapturePolicy<DateLayout>

const dateConstruction = {
  bindings: independentBindings,
  allocate: (node) =>
    adoptPrototype(new Date(node.layout.time), node.layout.prototype, Date.prototype),
} satisfies ConstructionPolicy<DateLayout>

export const dateSnapshot = /* @__PURE__ */ (() =>
  /* @__PURE__ */ freeze({
    ...dateCapture,
    snapshot(layout, _resolve, writer) {
      writer.initialize(
        layout,
        adoptPrototype(new Date(layout.time), layout.prototype, Date.prototype),
        noValue,
      )
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
      copy: (value) =>
        adoptPrototype(
          new Date((value as Date).getTime()),
          Object.getPrototypeOf(value) as object | null,
          Date.prototype,
        ),
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
  /** The source's prototype, which a copy keeps. */
  readonly prototype: object | null
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
