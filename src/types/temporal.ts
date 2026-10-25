import { EMPTY_FACTS } from '../constants'
import { adoptPrototype } from './shared/prototype'
import {
  freeze,
  independentBindings,
  independentDraft,
  noChildren,
  noDependencies,
  noValue,
  same,
} from './shared/empty'
import type {
  CapturePolicy,
  ConstructionPolicy,
  ImmutablePolicy,
  PublicationPolicy,
  SpecialPolicy,
  SnapshotPolicy,
} from '../types'
import { globalTemporal, temporalFrom } from '../standard-prototypes'
import { inChain } from '../object-property'

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

const TEMPORAL_CLASSES = [
  'Duration',
  'Instant',
  'PlainDate',
  'PlainDateTime',
  'PlainMonthDay',
  'PlainTime',
  'PlainYearMonth',
  'ZonedDateTime',
] as const

/** The first live Temporal class that `holds` accepts, in declared order; Temporal is read live. */
function temporalMatch(holds: (constructor: TemporalConstructor) => boolean) {
  const temporal = globalTemporal() as TemporalNamespace | null | undefined
  if (temporal == null) return undefined
  for (let index = 0; index < TEMPORAL_CLASSES.length; index += 1) {
    const constructor = temporal[TEMPORAL_CLASSES[index]]
    if (typeof constructor === 'function' && holds(constructor))
      return { temporalConstructor: constructor, temporalName: TEMPORAL_CLASSES[index] }
  }
  return undefined
}

/**
 * The Temporal class whose prototype is on the chain from `first`, a value's prototype already
 * read, probing each live class in order. The chain decides, as for every other kind: an
 * overridden `Symbol.hasInstance` does not.
 */
const temporalOf = (first: object | null) =>
  temporalMatch((constructor) => inChain(first, constructor))

/** The Temporal probe of built-in recognition from the prototype `first` already read. */
export const temporalInChain = (first: object | null): boolean => temporalOf(first) !== undefined

function equivalentValue(
  source: object,
  other: object,
  type: Pick<TemporalLayout, 'temporalConstructor' | 'temporalName'>,
): boolean {
  // Native copies discard instance shadows without losing Duration components or reference dates.
  const base = temporalFrom(type.temporalConstructor, type.temporalName, source)
  const candidate = temporalFrom(type.temporalConstructor, type.temporalName, other)
  if (type.temporalName === 'Duration') {
    for (let index = 0; index < durationFields.length; index += 1) {
      const field = durationFields[index]
      if ((base as Record<string, number>)[field] !== (candidate as Record<string, number>)[field])
        return false
    }
    return true
  }
  return (base as { equals: (other: object) => boolean }).equals(candidate)
}

/** Stores a detached native immutable value, retaining all native fields. */
export interface TemporalLayout {
  readonly kind: typeof TEMPORAL_KIND
  /** The source's prototype, which a copy keeps. */
  readonly prototype: object | null
  readonly temporalConstructor: TemporalConstructor
  readonly temporalName: (typeof TEMPORAL_CLASSES)[number]
  readonly temporalValue: object
}

function matches(layout: TemporalLayout, current: object): boolean {
  return (
    inChain(Object.getPrototypeOf(current) as object | null, layout.temporalConstructor) &&
    equivalentValue(layout.temporalValue, current, layout)
  )
}

/** Copies a Temporal value through its class's `from`, on the source's prototype. */
function copyTemporal(
  value: object,
  type: Pick<TemporalLayout, 'temporalConstructor' | 'temporalName'>,
  prototype: object | null,
): object {
  const constructor = type.temporalConstructor
  return adoptPrototype(
    temporalFrom(constructor, type.temporalName, value),
    prototype,
    constructor.prototype as object,
  )
}

const temporalCapture = {
  construction: noValue,
  observe(value, begin) {
    const prototype = Object.getPrototypeOf(value) as object | null
    const type = temporalOf(prototype)!
    begin({
      kind: TEMPORAL_KIND,
      ...type,
      prototype,
      temporalValue: copyTemporal(value, type, prototype),
    })
  },
} satisfies CapturePolicy<TemporalLayout>

const temporalConstruction = {
  bindings: independentBindings,
  allocate: (node) => copyTemporal(node.layout.temporalValue, node.layout, node.layout.prototype),
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
    seal: same,
    someChild: noChildren,
    // A Temporal value is kept only when equal.
    matches: (node, current) => matches(node.layout, current),
    requirements: (node, current) => (matches(node.layout, current) ? EMPTY_FACTS : undefined),
    // A Temporal value is never written: it is kept when equal, which readback would accept.
    publish(node, current, _resolve, _owner, note) {
      const kept = matches(node.layout, current)
      if (note !== undefined) note.unchanged = kept
      return kept
    },
  }))() satisfies PublicationPolicy<TemporalLayout>

export const temporalImmutable = /* @__PURE__ */ (() => ({
  immutable: /* @__PURE__ */ freeze({
    operations: /* @__PURE__ */ freeze({
      dependencies: noDependencies,
      copy(value) {
        const prototype = Object.getPrototypeOf(value) as object | null
        return copyTemporal(value, temporalOf(prototype)!, prototype)
      },
      equivalent(base, candidate) {
        const type = temporalOf(Object.getPrototypeOf(base) as object | null)!
        return (
          inChain(Object.getPrototypeOf(candidate) as object | null, type.temporalConstructor) &&
          equivalentValue(base, candidate, type)
        )
      },
    } satisfies SpecialPolicy),
    tag: 'copy',
  } satisfies ImmutablePolicy<TemporalLayout>['immutable']),
  someChild: noChildren,
}))() satisfies ImmutablePolicy<TemporalLayout>

export const temporalDraft = independentDraft
