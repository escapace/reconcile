import { snapshotValue, type SnapshotReceiver } from '../graph/edge'
import { adoptPrototype } from './shared/prototype'
import { arraySearches } from './shared/draft-members'
import { freeze, independentBindings, yes } from './shared/empty'
import { noValue } from './shared/empty'
import type {
  CapturePolicy,
  CapturedNode,
  ConstructionPolicy,
  DraftObservationContext,
  SnapshotPolicy,
  PublicationPolicy,
  ImmutablePolicy,
  DraftStrategy,
  Recognition,
} from '../types'
import { isObject, ownKeys } from '../object-property'
import { draftArrayIndexRejected, draftArrayLengthRejected } from '../error'
import { arrayIndex, hasOwn } from '../object-property'
import type { Edge } from '../types'
import { OBSERVED_ACCESSOR, UNREAD } from '../constants'
import { defineType } from './registry'
import type { PropertyDraftRules } from './shared/draft-properties'
import { PropertyDraftState, createPropertyHandle, writeDataSlot } from './shared/draft-properties'
import type { PropertySurface } from './shared/property-publication'
import {
  priorRead,
  propertyRequirements,
  propertySlots,
  publishProperty,
  publishRead,
  REFUSED,
  UNCHANGED,
  WROTE,
} from './shared/property-publication'

import { alignedProperties, backedProperty } from './shared/properties'
import { defineData, hasElement, isDataDescriptor } from '../standard-prototypes'

/** Stable global identity owned by the array module. */
export const ARRAY_KIND = Symbol.for('@escapace/reconcile/array')

const arraySurface: PropertySurface<ArrayLayout> = {
  desired: undefined,
  ordered: false,
  compatible(node, current, properties) {
    const prototype = Object.getPrototypeOf(current) as object | null
    const slots = properties()
    for (let index = 0; index < node.layout.length; index += 1)
      // A hole the array's own prototype fills cannot be published; one only a standard prototype
      // fills stays a hole, as hasElement reads it.
      if (
        !slots.has(String(index)) &&
        prototype !== null &&
        index in prototype &&
        !(index in Array.prototype)
      )
        return false
    return true
  },
  keys(value) {
    const keys: PropertyKey[] = []
    for (const key of ownKeys(value))
      if (key === 'length' || arrayIndex(key) !== undefined) keys.push(key)
    return keys
  },
  slots(node) {
    if (node.layout.slots !== undefined) return node.layout.slots
    const slots = propertySlots(node)
    slots.set('length', node.layout.length)
    return slots
  },
}

const arrayCapture = {
  construction: noValue,
  observe(value, begin, edge, mode) {
    const array = value as unknown[]
    const length = array.length
    begin({
      kind: ARRAY_KIND,
      length,
      prototype: Object.getPrototypeOf(array) as object | null,
      slots: undefined,
    })
    // A snapshot only writes the element, and a numeric key names the same property.
    for (let index = 0; index < array.length; index += 1)
      if (hasElement(array, index)) edge(array[index], mode === 'snapshot' ? index : String(index))
  },
} satisfies CapturePolicy<ArrayLayout>

const arrayConstruction = {
  bindings: independentBindings,
  allocate: (node) =>
    adoptPrototype(new Array<unknown>(node.layout.length), node.layout.prototype, Array.prototype),
} satisfies ConstructionPolicy<ArrayLayout>

/**
 * Writes an element into a new copy: by assignment when the copy is a standard array, otherwise
 * as an own data property, so no setter on a subclass's prototype runs.
 */
function fillElement(
  target: object,
  prototype: object | null,
  key: PropertyKey,
  value: unknown,
): void {
  if (prototype === Array.prototype) (target as Record<PropertyKey, unknown>)[key] = value
  else defineData(target, key, value)
}

// Writes one snapshot element into the receiving reference's target.
function writeArraySlot(this: SnapshotReceiver, edge: Edge, key: PropertyKey | undefined): void {
  const target = this.target!
  fillElement(target, Object.getPrototypeOf(target) as object | null, key!, snapshotValue(edge))
}

export const arraySnapshot = /* @__PURE__ */ (() =>
  /* @__PURE__ */ freeze({
    ...arrayCapture,
    snapshot(layout, _resolve, writer) {
      writer.initialize(
        layout,
        adoptPrototype(new Array<unknown>(layout.length), layout.prototype, Array.prototype),
        writeArraySlot,
      )
    },
  }))() satisfies SnapshotPolicy<ArrayLayout>

// What the call already read at edge `edge`, which holds `key`, or `UNREAD`.
const readAt = (
  node: CapturedNode<ArrayLayout>,
  reads: readonly unknown[] | undefined,
  edge: number,
  key: string,
  held: ReadonlyMap<PropertyKey, unknown> | undefined,
): unknown => priorRead(node.keys[edge] === key ? reads : undefined, edge, held, key)

export const arrayPublication = /* @__PURE__ */ (() =>
  /* @__PURE__ */ freeze({
    ...arrayCapture,
    ...arrayConstruction,
    aligned: alignedProperties,
    compatible: yes,
    matches(node, current, visit) {
      const array = current as unknown[]
      const length = node.layout.length
      if (array.length !== length) return false
      const properties = arraySurface.slots(node)
      for (let index = 0; index < length; index += 1) {
        const key = String(index)
        const present = properties.has(key)
        if (hasOwn(array, index) !== present || hasElement(array, index) !== present) return false
        if (present && !visit(array[index], properties.get(key))) return false
      }
      return true
    },
    // fallow-ignore-next-line complexity -- a dispatch helper per element slowed reconcile 3%
    publish(node, target, image, _owner, note) {
      const properties = arraySurface.slots(node)
      const length = node.layout.length
      let written = publishProperty(target, 'length', length)
      if (written === REFUSED) return false
      // The reads, capture's or a previous readback's, follow the edges: present indices in order.
      const reads = note?.reads
      // The fixed slots a preflight of this publication read, by key.
      const held = note?.held?.get(target)
      let edge = 0
      for (let index = 0; index < length; index += 1) {
        const key = String(index)
        if (properties.has(key)) {
          const read = readAt(node, reads, edge, key, held)
          edge += 1
          const value = image(properties.get(key))
          const element =
            read === UNREAD
              ? publishProperty(target, key, value)
              : publishRead(target, key, value, undefined, read)
          if (element === REFUSED) return false
          if (element === WROTE) written = WROTE
        } else if (hasOwn(target, index)) {
          if (!Reflect.deleteProperty(target, key)) return false
          written = WROTE
        }
      }
      // The length, every element and every hole already held: readback would accept
      // (WriteFreeReadback.array_writeFree_matches).
      if (note !== undefined) note.unchanged = written === UNCHANGED
      return true
    },
    // The note serves only the fixed slots' reads: an array's publication takes no other facts.
    requirements: (node, current, note) =>
      propertyRequirements(node, current, arraySurface, undefined, note),
    // The building node and its layout are private to this capture; seal indexes them in place.
    seal(node) {
      let length = node.layout.length
      for (const key of node.keys) length = Math.max(length, Number(key) + 1)
      const slots = propertySlots(node)
      slots.set('length', length)
      const layout = node.layout as { length: number; slots?: ReadonlyMap<PropertyKey, Edge> }
      layout.length = length
      layout.slots = slots
      return node
    },
  }))() satisfies PublicationPolicy<ArrayLayout>

// Observes one index of an array or its draft. An index the array does not own is an element
// only when its prototype, other than the standard one, supplies it; an own getter is marked, as
// on objects, so reuse can keep it.
function observeElement(
  array: unknown[],
  index: number,
  observer: DraftObservationContext<ArrayLayout>,
): void {
  const properties = observer.properties
  const key = String(index)
  const own =
    properties === undefined
      ? Object.getOwnPropertyDescriptor(array, key)
      : properties.ownDescriptor(key)
  if (
    own === undefined &&
    !(properties === undefined
      ? hasElement(array, index)
      : properties.contains(key) && !(index in Array.prototype))
  )
    return
  const data = own !== undefined && isDataDescriptor(own)
  const value = !data
    ? observer.read(array, key)
    : properties === undefined
      ? (Reflect.get(array, key) as unknown)
      : properties.ownValue(key, own)
  observer.edge(
    value,
    key,
    isObject(value) && backedProperty(observer.base, key, value),
    data || own === undefined ? undefined : OBSERVED_ACCESSOR,
  )
}

export const arrayImmutable = /* @__PURE__ */ (() => ({
  ...arrayConstruction,
  immutable: /* @__PURE__ */ freeze({
    tag: 'structural',
    observeDraft(source, observer) {
      const properties = observer.properties
      const array = source as unknown[]
      const length = (): number =>
        properties === undefined ? array.length : (properties.read('length') as number)
      const size = new Array(length()).length
      const prototype =
        properties === undefined
          ? (Object.getPrototypeOf(source) as object | null)
          : properties.sourcePrototype()
      observer.begin({ kind: ARRAY_KIND, length: size, prototype, slots: undefined })
      for (let index = 0; index < length(); index += 1) observeElement(array, index, observer)
    },
    reuse(node, current, visit) {
      const array = current as unknown[]
      if (array.length !== node.layout.length) return false
      let position = 0
      for (let index = 0; index < array.length; index += 1) {
        const descriptor = Object.getOwnPropertyDescriptor(current, index)
        if (descriptor === undefined) continue
        if (node.keys[position] !== String(index)) return false
        // An own getter observed in this call stays as on objects (DraftSurface.keeps).
        if (
          isDataDescriptor(descriptor)
            ? !visit(array[index], node.edges[position])
            : ((node.attributes?.[position] ?? 0) & OBSERVED_ACCESSOR) === 0 ||
              !visit(node.observed?.[position], node.edges[position])
        )
          return false
        position += 1
      }
      return position === node.keys.length
    },
  } satisfies ImmutablePolicy<ArrayLayout>['immutable']),
  freshWrite(node, target, index, resolve) {
    fillElement(target, node.layout.prototype, node.keys[index], resolve(node.edges[index]))
  },
  someChild(source, read, test) {
    const array = source as unknown[]
    for (let index = 0; index < array.length; index += 1)
      if (hasElement(array, index) && test(read(source, String(index)))) return true
    return false
  },
}))() satisfies ImmutablePolicy<ArrayLayout>

const arrayPolicy = /* @__PURE__ */ (() => ({
  ...arraySnapshot,
  ...arrayPublication,
  ...arrayImmutable,
}))()

/** Captures array length and an optional sealed index; holes are absent edge keys. */
// fallow-ignore-next-line unused-type -- part of the declared type of builtinModules in builtins.ts
export interface ArrayLayout {
  readonly kind: typeof ARRAY_KIND
  readonly length: number
  /** The source's prototype, which a copy keeps. */
  readonly prototype: object | null
  readonly slots: ReadonlyMap<PropertyKey, Edge> | undefined
}

/**
 * Applies native array-length coercion and descending index deletion to the descriptor store.
 *
 * @remarks
 * Coerces object inputs twice before reading the old length. A fixed index stops truncation and
 * leaves the length immediately above that index, including when the write fails.
 *
 * @returns Whether the requested length can be applied.
 * @throws RangeError when numeric coercions do not describe a valid array length.
 */
function writeArrayLength(copy: Record<PropertyKey, PropertyDescriptor>, value: unknown): boolean {
  // ArraySetLength deliberately coerces object values twice, before reading old length.
  const length = (value as number) >>> 0
  if (length !== +(value as number)) throw new RangeError('Invalid array length')
  const descriptor = copy.length
  const previous = descriptor.value as number
  if (descriptor.writable === false) return Object.is(length, previous)
  descriptor.value = length
  if (length >= previous) return true
  const keys = Object.getOwnPropertyNames(copy)
  for (let position = keys.length - 1; position >= 0; position -= 1) {
    const key = keys[position]
    const index = arrayIndex(key)
    if (index === undefined || index < length) continue
    if (copy[key].configurable === false) {
      descriptor.value = index + 1
      return false
    }
    delete copy[key]
  }
  return true
}

const arrayDraftRules: PropertyDraftRules<typeof ARRAY_KIND> = {
  kind: ARRAY_KIND,
  methods: arraySearches,
  admits: (key) => key === 'length' || arrayIndex(key) !== undefined,
  capture(copy, key, descriptor) {
    if (key === 'length') {
      if (!writeArrayLength(copy, descriptor.value))
        throw draftArrayLengthRejected(descriptor.value as number)
      descriptor.value = copy.length.value as unknown
    } else {
      const index = arrayIndex(key)
      if (index !== undefined && index >= (copy.length.value as number)) {
        if (copy.length.writable === false) throw draftArrayIndexRejected(index)
        copy.length.value = index + 1
      }
    }
  },
  configurable: (property) => property !== 'length',
  initialize(source, copy) {
    const argument = source.length
    const length = typeof argument === 'number' ? argument : 1
    if (length >>> 0 !== length) throw new RangeError('Invalid array length')
    copy.length = { configurable: false, enumerable: false, value: length, writable: true }
    if (typeof argument !== 'number')
      copy[0] = { configurable: true, enumerable: true, value: argument, writable: true }
  },
  target: () => new Array<unknown>(),
  write(state, copy, property, value) {
    const previousLength = copy.length.value as number
    if (property === 'length') {
      const written = writeArrayLength(copy, value)
      if (copy.length.value !== previousLength) state.modified = true
      return written
    }
    const index = arrayIndex(property)
    // Like a non-extensible object, refuse what an array result cannot carry (admits).
    if (index === undefined) return false
    if (index >= previousLength && copy.length.writable === false) return false
    if (!writeDataSlot(copy, property, value)) return false
    if (index >= previousLength) copy.length.value = index + 1
    return true
  },
}

export const arrayDraft = /* @__PURE__ */ freeze({
  tag: 'structural',
  handle: (state) => createPropertyHandle(state),
  state: (base, context) => new PropertyDraftState(base, context, arrayDraftRules),
}) satisfies DraftStrategy<PropertyDraftState<typeof ARRAY_KIND>>

export const arrayRecognition = /* @__PURE__ */ freeze({
  tag: 'predicate',
  test: Array.isArray,
}) satisfies Recognition

export const arrayType = /* @__PURE__ */ defineType<
  ArrayLayout,
  PropertyDraftState<typeof ARRAY_KIND>
>({
  draft: arrayDraft,
  kind: ARRAY_KIND,
  name: 'array',
  policy: arrayPolicy,
  recognition: arrayRecognition,
})
