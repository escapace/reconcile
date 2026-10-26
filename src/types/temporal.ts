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
import {
  inChain,
  knownPrototype,
  type PrototypeRead,
  type TemporalClass,
  type TemporalConstructor,
} from '../object-property'

/** The Temporal kind. */
export const TEMPORAL_KIND = Symbol('temporal')

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
function temporalMatch(
  holds: (constructor: TemporalConstructor) => boolean,
): TemporalClass | undefined {
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

/**
 * The Temporal probe of built-in recognition from the prototype `first` already read. The class it
 * finds is kept in `read`, so the value's capture does not probe the classes again
 * (Types.Ingress.temporalCapture_passed).
 */
export function temporalInChain(first: object | null, read: PrototypeRead | undefined): boolean {
  const type = temporalOf(first)
  if (type === undefined) return false
  if (read !== undefined) read.temporal = type
  return true
}

function equivalentValue(source: object, other: object, type: TemporalClass): boolean {
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
export interface TemporalLayout extends TemporalClass {
  readonly kind: typeof TEMPORAL_KIND
  /** The source's prototype, which a copy keeps. */
  readonly prototype: object | null
  readonly temporalValue: object
}

function matches(layout: TemporalLayout, current: object): boolean {
  return (
    inChain(Object.getPrototypeOf(current) as object | null, layout.temporalConstructor) &&
    equivalentValue(layout.temporalValue, current, layout)
  )
}

/** Copies a Temporal value through its class's `from`, on the source's prototype. */
function copyTemporal(value: object, type: TemporalClass, prototype: object | null): object {
  const constructor = type.temporalConstructor
  return adoptPrototype(
    temporalFrom(constructor, type.temporalName, value),
    prototype,
    constructor.prototype as object,
  )
}

const temporalCapture = {
  construction: noValue,
  // The prototype and class recognition found, when its caller passes them.
  observe(value, begin, _edge, _mode, known, found) {
    const prototype = knownPrototype(value, known)
    const type = found ?? temporalOf(prototype)!
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
    snapshot: (layout) => layout.temporalValue,
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
    // A Temporal value is never written: a kept one passed the preflight's comparison, which
    // every pass reruns, and a new one is a copy, so readback would accept either.
    publish(_node, _current, _resolve, _owner, note) {
      if (note !== undefined) note.unchanged = true
      return true
    },
  }))() satisfies PublicationPolicy<TemporalLayout>

export const temporalImmutable = /* @__PURE__ */ (() => ({
  immutable: /* @__PURE__ */ freeze({
    operations: /* @__PURE__ */ freeze({
      dependencies: noDependencies,
      copy(value, _resolve, _owners, known, found) {
        const prototype = knownPrototype(value, known)
        return copyTemporal(value, found ?? temporalOf(prototype)!, prototype)
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
