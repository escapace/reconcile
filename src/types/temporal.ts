import {
  emptyEdges,
  freeze,
  independentBindings,
  independentDraft,
  noChildren,
  noDependencies,
  noValue,
  ordinaryExposure,
  same,
} from './shared/empty'
import type {
  CapturePolicy,
  ConstructionPolicy,
  ImmutablePolicy,
  PublicationPolicy,
  Recognition,
  SnapshotPolicy,
  SpecialPolicy,
} from '../types'
import { defineType } from './registry'

/** Stable global identity owned by the Temporal module. */
export const TEMPORAL_KIND = Symbol.for('@escapace/reconcile/temporal')

const durationFields = [
  'years',
  'months',
  'weeks',
  'days',
  'hours',
  'minutes',
  'seconds',
  'milliseconds',
  'microseconds',
  'nanoseconds',
] as const

export interface TemporalConstructor {
  new (...arguments_: never[]): object
  from: (value: object) => object
}

type TemporalNamespace = Partial<
  Record<
    | 'Duration'
    | 'Instant'
    | 'PlainDate'
    | 'PlainDateTime'
    | 'PlainMonthDay'
    | 'PlainTime'
    | 'PlainYearMonth'
    | 'ZonedDateTime',
    TemporalConstructor
  >
>

/** Static probes preserve native property and instanceof order; Temporal is read live. */
function temporalClass(value: object) {
  const temporal = (globalThis as { Temporal?: TemporalNamespace | null }).Temporal
  if (temporal == null) return undefined
  let constructor = temporal.Duration
  if (typeof constructor === 'function' && value instanceof constructor)
    return { temporalConstructor: constructor, temporalDuration: true }
  constructor = temporal.Instant
  if (typeof constructor === 'function' && value instanceof constructor)
    return { temporalConstructor: constructor, temporalDuration: false }
  constructor = temporal.PlainDate
  if (typeof constructor === 'function' && value instanceof constructor)
    return { temporalConstructor: constructor, temporalDuration: false }
  constructor = temporal.PlainDateTime
  if (typeof constructor === 'function' && value instanceof constructor)
    return { temporalConstructor: constructor, temporalDuration: false }
  return temporalRemainingClass(value, temporal)
}

/** Continues the eight-probe trace without a per-value continuation allocation. */
function temporalRemainingClass(value: object, temporal: TemporalNamespace) {
  let constructor = temporal.PlainMonthDay
  if (typeof constructor === 'function' && value instanceof constructor)
    return { temporalConstructor: constructor, temporalDuration: false }
  constructor = temporal.PlainTime
  if (typeof constructor === 'function' && value instanceof constructor)
    return { temporalConstructor: constructor, temporalDuration: false }
  constructor = temporal.PlainYearMonth
  if (typeof constructor === 'function' && value instanceof constructor)
    return { temporalConstructor: constructor, temporalDuration: false }
  constructor = temporal.ZonedDateTime
  if (typeof constructor === 'function' && value instanceof constructor)
    return { temporalConstructor: constructor, temporalDuration: false }
  return undefined
}

function equivalentValue(
  source: object,
  other: object,
  type: Pick<TemporalLayout, 'temporalConstructor' | 'temporalDuration'>,
): boolean {
  // Native copies discard instance shadows without losing Duration components or reference dates.
  const base = type.temporalConstructor.from(source)
  const candidate = type.temporalConstructor.from(other)
  if (type.temporalDuration) {
    for (const field of durationFields)
      if ((base as Record<string, number>)[field] !== (candidate as Record<string, number>)[field])
        return false
    return true
  }
  return (base as { equals: (other: object) => boolean }).equals(candidate)
}

/** Stores a detached native immutable value, retaining all native fields. */
export interface TemporalLayout {
  readonly kind: typeof TEMPORAL_KIND
  readonly temporalConstructor: TemporalConstructor
  readonly temporalDuration: boolean
  readonly temporalValue: object
}

function matches(layout: TemporalLayout, current: object): boolean {
  return (
    current instanceof layout.temporalConstructor &&
    equivalentValue(layout.temporalValue, current, layout)
  )
}

const temporalCapture = {
  construction: noValue,
  observe(value, begin) {
    const type = temporalClass(value)!
    begin({
      kind: TEMPORAL_KIND,
      ...type,
      temporalValue: type.temporalConstructor.from(value),
    })
  },
} satisfies CapturePolicy<TemporalLayout>

const temporalConstruction = {
  bindings: independentBindings,
  allocate: (node) => node.layout.temporalConstructor.from(node.layout.temporalValue),
} satisfies ConstructionPolicy<TemporalLayout>

export const temporalSnapshot = /* @__PURE__ */ (() =>
  /* @__PURE__ */ freeze({
    ...temporalCapture,
    snapshot(layout, _resolve, writer) {
      writer.initialize(layout, layout.temporalValue, noValue)
    },
  }))() satisfies SnapshotPolicy<TemporalLayout>

export const temporalPublication = /* @__PURE__ */ (() =>
  /* @__PURE__ */ freeze({
    ...temporalCapture,
    ...temporalConstruction,
    aligned: noValue,
    requirements: emptyEdges,
    seal: same,
    compatible: (node, current) => matches(node.layout, current),
    matches: (node, current) => matches(node.layout, current),
    publish: (node, current) => matches(node.layout, current),
  }))() satisfies PublicationPolicy<TemporalLayout>

export const temporalImmutable = /* @__PURE__ */ (() => ({
  ...temporalConstruction,
  freshWrite: noValue,
  immutable: /* @__PURE__ */ freeze({
    operations: /* @__PURE__ */ freeze({
      dependencies: noDependencies,
      copy: (value) => temporalClass(value)!.temporalConstructor.from(value),
      equivalent(base, candidate) {
        const type = temporalClass(base)!
        return (
          candidate instanceof type.temporalConstructor && equivalentValue(base, candidate, type)
        )
      },
    } satisfies SpecialPolicy),
    tag: 'copy',
  } satisfies ImmutablePolicy<TemporalLayout>['immutable']),
  someChild: noChildren,
}))() satisfies ImmutablePolicy<TemporalLayout>

const temporalPolicy = /* @__PURE__ */ (() => ({
  ...temporalSnapshot,
  ...temporalPublication,
  ...temporalImmutable,
}))()

export const temporalDraft = independentDraft
export const temporalExposure = ordinaryExposure
export const temporalRecognition = /* @__PURE__ */ freeze({
  tag: 'predicate',
  test: (value: object) => temporalClass(value) !== undefined,
}) satisfies Recognition

export const temporalType = /* @__PURE__ */ defineType<TemporalLayout>({
  draft: temporalDraft,
  exposure: temporalExposure,
  kind: TEMPORAL_KIND,
  name: 'temporal',
  policy: temporalPolicy,
  recognition: temporalRecognition,
})
