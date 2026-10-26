import { builtinValue, uncurried } from '../standard-prototypes'
import { adoptPrototype } from './shared/prototype'
import { freeze, independentBindings, same } from './shared/empty'
import type { SpecialPolicy } from '../types'
import { independentDraft } from './shared/empty'
import { noValue } from './shared/empty'
import type {
  CapturePolicy,
  ConstructionPolicy,
  PublicationPolicy,
  ImmutablePolicy,
} from '../types'
import { emptyEdges, noChildren, noDependencies } from './shared/empty'
import { knownPrototype } from '../object-property'

// The built-in time accessors: a subclass override or a patched prototype is never called, as
// for buffers and URLs.
const dateSetTime = /* @__PURE__ */ (() =>
  uncurried<[time: number], number>(builtinValue(Date.prototype, 'setTime')))()

/** A date's time, read with the built-in method. */
export const timeOf = /* @__PURE__ */ (() =>
  uncurried<[], number>(builtinValue(Date.prototype, 'getTime')))() as (value: object) => number

/** The `Date` kind. */
export const DATE_KIND = Symbol('date')

const dateCapture = {
  construction: noValue,
  observe(value, begin, _edge, _mode, known) {
    const time = timeOf(value)
    begin({ kind: DATE_KIND, prototype: knownPrototype(value, known), time })
  },
} satisfies CapturePolicy<DateLayout>

const dateConstruction = {
  bindings: independentBindings,
  allocate: (node) =>
    adoptPrototype(new Date(node.layout.time), node.layout.prototype, Date.prototype),
} satisfies ConstructionPolicy<DateLayout>

export const datePublication = /* @__PURE__ */ (() =>
  /* @__PURE__ */ freeze({
    ...dateCapture,
    ...dateConstruction,
    aligned: noValue,
    requirements: emptyEdges,
    seal: same,
    someChild: noChildren,
    matches: (node, current) => Object.is(timeOf(current), node.layout.time),
    // Only a changed time is written; a publication that wrote nothing found it equal, as readback,
    // which compares the same time, would.
    publish(node, current, _resolve, _owner, note) {
      const equal = Object.is(timeOf(current), node.layout.time)
      if (!equal) dateSetTime(current, node.layout.time)
      if (note !== undefined) note.unchanged = equal
      return true
    },
  }))() satisfies PublicationPolicy<DateLayout>

export const dateImmutable = /* @__PURE__ */ (() => ({
  immutable: /* @__PURE__ */ freeze({
    operations: /* @__PURE__ */ freeze({
      dependencies: noDependencies,
      copy: (value, _resolve, _owners, known) =>
        adoptPrototype(new Date(timeOf(value)), knownPrototype(value, known), Date.prototype),
      equivalent: (base, candidate) => Object.is(timeOf(base), timeOf(candidate)),
    } satisfies SpecialPolicy),
    tag: 'copy',
  } satisfies ImmutablePolicy<DateLayout>['immutable']),
  someChild: noChildren,
}))() satisfies ImmutablePolicy<DateLayout>

/** Stores the captured native timestamp, including an invalid-date NaN. */
export interface DateLayout {
  readonly kind: typeof DATE_KIND
  /** The source's prototype, which a copy keeps. */
  readonly prototype: object | null
  readonly time: number
}

export const dateDraft = independentDraft
