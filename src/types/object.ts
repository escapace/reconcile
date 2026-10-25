import { OBJECT_KIND, OBSERVED_ACCESSOR, UNREAD } from '../constants'
import { snapshotValue, type SnapshotReceiver } from '../graph/edge'
import { freeze, independentBindings, noValue, same, yes } from './shared/empty'
import type {
  CapturedNode,
  CapturePolicy,
  ConstructionPolicy,
  SnapshotPolicy,
  PublicationPolicy,
  ImmutablePolicy,
  DraftObservationContext,
  DraftStrategy,
  Recognition,
} from '../types'
import { hasOwn, hiddenNames, isObject, ownKeys } from '../object-property'
import { setOwnProperty, standardPrototype } from '../set-own-property'
import type { Edge } from '../types'
import { defineType } from './registry'
import type { PropertyDraftRules } from './shared/draft-properties'
import { createPropertyHandle, PropertyDraftState, writeDataSlot } from './shared/draft-properties'
import type { PropertySurface } from './shared/property-publication'
import {
  alignedPrefix,
  priorRead,
  PropertyOrder,
  propertyRequirements,
  propertySlots,
  publishKnown,
  publishRead,
  REFUSED,
  UNCHANGED,
  WROTE,
  wrote,
} from './shared/property-publication'

import { alignedProperties, backedProperty } from './shared/properties'
import { defineData, hide, isDataDescriptor, restoreAttributes } from '../standard-prototypes'

/** Stable global identity owned by the object module. */
export { OBJECT_KIND }

const objectSurface: PropertySurface<ObjectLayout> = {
  compatible: yes,
  keys: ownKeys,
  ordered: true,
  desired: (node) => node.keys,
  // The layout is private to this call's capture; the index is built on first demand.
  slots: (node) =>
    node.layout.slots ??
    ((node.layout as { slots?: ReadonlyMap<PropertyKey, Edge> }).slots = propertySlots(node)),
}

const objectCapture = {
  construction: noValue,
  // A caller that classified the value passes the prototype it read.
  observe(value, begin, edge, _mode, known) {
    const prototype = known === undefined ? (Object.getPrototypeOf(value) as object | null) : known
    const names = Object.getOwnPropertyNames(value)
    const layout: ObjectLayout = {
      hidden: hiddenNames(value, names),
      kind: OBJECT_KIND,
      prototype,
      slots: undefined,
    }
    begin(layout)
    // Symbols are listed after string getters run, so keys those getters add are captured. A
    // symbol is read after its descriptor, as `hiddenNames` reads the names', so one a proxy lists
    // without a descriptor is absent.
    for (let index = 0; index < names.length; index += 1)
      edge(Reflect.get(value, names[index]) as unknown, names[index])
    const symbols = Object.getOwnPropertySymbols(value)
    for (let index = 0; index < symbols.length; index += 1) {
      const key = symbols[index]
      const descriptor = Object.getOwnPropertyDescriptor(value, key)
      if (descriptor === undefined) continue
      edge(Reflect.get(value, key) as unknown, key)
      if (descriptor.enumerable !== true)
        ((layout as { hidden?: Set<PropertyKey> }).hidden ??= new Set()).add(key)
    }
  },
} satisfies CapturePolicy<ObjectLayout>

const objectConstruction = {
  bindings: independentBindings,
  allocate: (node) => Object.create(node.layout.prototype) as object,
} satisfies ConstructionPolicy<ObjectLayout>

// Writes one snapshot property into a new object on `Object.prototype` or a null prototype.
function writeStandardSlot(this: SnapshotReceiver, edge: Edge, key: PropertyKey | undefined): void {
  setOwnProperty(
    this.target as Record<PropertyKey, unknown>,
    key!,
    snapshotValue(edge),
    true,
    (this.layout as ObjectLayout).hidden?.has(key!) !== true,
  )
}

// Writes one snapshot property into a new object on any other prototype, by definition.
function writeDefinedSlot(this: SnapshotReceiver, edge: Edge, key: PropertyKey | undefined): void {
  setOwnProperty(
    this.target as Record<PropertyKey, unknown>,
    key!,
    snapshotValue(edge),
    false,
    (this.layout as ObjectLayout).hidden?.has(key!) !== true,
  )
}

const objectSnapshot = /* @__PURE__ */ (() =>
  /* @__PURE__ */ freeze({
    ...objectCapture,
    snapshot(layout, _resolve, writer) {
      writer.initialize(
        layout,
        Object.create(layout.prototype) as object,
        standardPrototype(layout.prototype) ? writeStandardSlot : writeDefinedSlot,
      )
    },
  }))() satisfies SnapshotPolicy<ObjectLayout>

/** Writes each requested property in order. A property this write adds takes next's
 * enumerability, so a hidden one stays hidden; an existing one keeps its own attributes, and so
 * does one `deleteUnrequested` deleted to move it (`moved`): it is assigned, as application code
 * writes it, and then takes its attributes again. `known` holds the preflight's
 * descriptor for each requested key the target already had in the same position. Returns
 * `REFUSED`, `WROTE`, or `UNCHANGED` when no key was written. */
// fallow-ignore-next-line complexity -- a dispatch helper per key slowed reconcile 3%
function writeProperties(
  node: CapturedNode<ObjectLayout>,
  target: object,
  image: (edge: Edge) => unknown,
  known: ReadonlyArray<PropertyDescriptor | undefined> | undefined,
  reads: readonly unknown[] | undefined,
  removed: readonly PropertyKey[] | undefined,
  moved: readonly unknown[] | undefined,
): number {
  const hidden = node.layout.hidden
  const lookup = reads !== undefined
  let result = UNCHANGED
  for (let index = 0; index < node.keys.length; index += 1) {
    const key = node.keys[index]
    const descriptor = known !== undefined && index < known.length ? known[index] : undefined
    const before = moved === undefined || moved.length === 0 ? undefined : movedFrom(moved, key)
    const added =
      before === undefined &&
      descriptor === undefined &&
      hidden?.has(key) === true &&
      !hasOwn(target, key)
    const read = lookup ? priorRead(reads, index, key, removed) : UNREAD
    const value = image(node.edges[index])
    // Without a read the key takes `publishKnown` as it is, kept small enough to inline.
    const written =
      read === UNREAD
        ? publishKnown(target, key, value, descriptor)
        : publishRead(target, key, value, descriptor, read)
    if (written === REFUSED) return REFUSED
    if (written === WROTE) result = WROTE
    if (added && !hide(target, key)) return REFUSED
    if (
      before !== undefined &&
      (before.enumerable !== true || before.writable !== true) &&
      !restoreAttributes(target, key, before.enumerable === true, before.writable === true)
    )
      return REFUSED
  }
  return result
}

/** Deletes the current keys the requested order does not keep: past the requested count in the
 * aligned order, otherwise unrequested or configurable and out of order. Returns `REFUSED`,
 * `WROTE` when it deleted a key, or `UNCHANGED`; each requested key it deleted is added to
 * `removed`, when given, and with its data descriptor to `moved`. */
function deleteUnrequested(
  target: object,
  previous: readonly PropertyKey[],
  requested: number,
  properties: ReadonlyMap<PropertyKey, Edge> | undefined,
  removed: PropertyKey[] | undefined,
  moved: unknown[] | undefined,
): number {
  const order = properties === undefined ? undefined : new PropertyOrder(properties)
  let result = UNCHANGED
  for (let position = 0; position < previous.length; position += 1) {
    const key = previous[position]
    const retained = order?.keep(key)
    const unrequested = !(properties === undefined ? position < requested : properties.has(key))
    const deleted = unrequested
      ? wrote(Reflect.deleteProperty(target, key))
      : retained === false
        ? moveKey(target, key, removed, moved)
        : UNCHANGED
    if (deleted === REFUSED) return REFUSED
    if (deleted === WROTE) result = WROTE
  }
  return result
}

/** Deletes a requested key that is out of order so that it can move, recording it in `removed`
 * and, followed by its data descriptor, in `moved`; a non-configurable key stays. */
function moveKey(
  target: object,
  key: PropertyKey,
  removed: PropertyKey[] | undefined,
  moved: unknown[] | undefined,
): number {
  const descriptor = Object.getOwnPropertyDescriptor(target, key)
  if (descriptor?.configurable === false) return UNCHANGED
  if (!Reflect.deleteProperty(target, key)) return REFUSED
  removed?.push(key)
  if (descriptor !== undefined && isDataDescriptor(descriptor)) moved?.push(key, descriptor)
  return WROTE
}

/** The descriptor `moveKey` recorded for `key` in `moved`, or undefined. */
function movedFrom(moved: readonly unknown[], key: PropertyKey): PropertyDescriptor | undefined {
  for (let index = 0; index < moved.length; index += 2)
    if (moved[index] === key) return moved[index + 1] as PropertyDescriptor
  return undefined
}

export const objectPublication = /* @__PURE__ */ (() =>
  /* @__PURE__ */ freeze({
    ...objectCapture,
    ...objectConstruction,
    aligned: alignedProperties,
    // The key list must match before any value is read, so no key is read through the
    // prototype; every value is then read once, whether or not an earlier one matched.
    matches(node, current, visit) {
      const keys = ownKeys(current)
      if (keys.length !== node.keys.length) return false
      for (let index = 0; index < keys.length; index += 1)
        if (keys[index] !== node.keys[index]) return false
      let matched = true
      for (let index = 0; index < keys.length; index += 1)
        if (!visit(Reflect.get(current, node.keys[index]), node.edges[index])) matched = false
      return matched
    },
    publish(node, target, image, _owner, note) {
      const keys = node.keys
      // The first publication of an ordinary target reuses the preflight's key list.
      const facts = note?.facts
      const previous = facts?.keys ?? ownKeys(target)
      // Own keys are duplicate-free, so when they start with the requested order exactly the
      // first keys.length of them are requested (PropertyOrder.aligned_mem), and requested key
      // i holds edge i.
      const properties = alignedPrefix(previous, keys) ? undefined : objectSurface.slots(node)
      // The reads, capture's or a previous readback's, follow the node's edges; a requested key
      // moved into the requested order is deleted first, and its read no longer holds.
      const reads = note?.reads
      const removed = reads !== undefined && properties !== undefined ? [] : undefined
      const moved: unknown[] | undefined = properties === undefined ? undefined : []
      const deleted = deleteUnrequested(target, previous, keys.length, properties, removed, moved)
      if (deleted === REFUSED) return false
      // In the aligned order, descriptor i belongs to requested key i.
      const written = writeProperties(
        node,
        target,
        image,
        properties === undefined ? facts?.descriptors : undefined,
        reads,
        removed,
        moved,
      )
      // Aligned, nothing deleted and no key written: readback would accept
      // (WriteFreeReadback.object_writeFree_matches).
      if (note !== undefined)
        note.unchanged = written === UNCHANGED && properties === undefined && deleted === UNCHANGED
      return written !== REFUSED
    },
    requirements: (node, current, note) => propertyRequirements(node, current, objectSurface, note),
    // Object slots are indexed on first demand; see objectSurface.
    seal: same,
  }))() satisfies PublicationPolicy<ObjectLayout>

// Packs a data descriptor's configurable, enumerable and writable flags into bits 1, 2 and 4.
const attributeBits = (descriptor: PropertyDescriptor): number =>
  (descriptor.configurable === true ? 1 : 0) |
  (descriptor.enumerable === true ? 2 : 0) |
  (descriptor.writable === true ? 4 : 0)

// Packs an own accessor's enumerable flag; an observed accessor is otherwise a configurable,
// writable data slot of the copy.
const accessorBits = (descriptor: PropertyDescriptor): number =>
  OBSERVED_ACCESSOR | 5 | (descriptor.enumerable === false ? 0 : 2)

// Observes one own key of an object or its draft: its value, its attributes and whether `base`
// backs it, which reads of `base` itself (`fromBase`) already answer.
function observeSlot(
  source: object,
  key: PropertyKey,
  observer: DraftObservationContext<ObjectLayout>,
  fromBase: boolean,
): void {
  const { base, properties } = observer
  const descriptor =
    properties === undefined
      ? Object.getOwnPropertyDescriptor(source, key)
      : properties.ownDescriptor(key)
  // A key a proxy lists without a descriptor is absent, as `Object.keys` treats it.
  if (descriptor === undefined) return
  const data = isDataDescriptor(descriptor)
  const value: unknown = data
    ? properties === undefined
      ? Reflect.get(source, key)
      : properties.ownValue(key, descriptor)
    : observer.read(source, key)
  observer.edge(
    value,
    key,
    (isObject(value) || !data) && (fromBase ? data : backedProperty(base, key, value)),
    data ? attributeBits(descriptor) : accessorBits(descriptor),
  )
}

export const objectImmutable = /* @__PURE__ */ (() => ({
  ...objectConstruction,
  immutable: /* @__PURE__ */ freeze({
    tag: 'structural',
    observeDraft(source, observer) {
      const { base, properties } = observer
      const prototype =
        properties === undefined
          ? (Object.getPrototypeOf(source) as object | null)
          : properties.sourcePrototype()
      observer.begin({ hidden: undefined, kind: OBJECT_KIND, prototype, slots: undefined })
      const keys = properties === undefined ? ownKeys(source) : properties.keys(source)
      // Reads of the object itself answer whether a slot is backed by it, as reading it again
      // would.
      const fromBase =
        base !== undefined && (properties === undefined ? source === base : properties.readsBase())
      for (let index = 0; index < keys.length; index += 1)
        observeSlot(source, keys[index], observer, fromBase)
    },
    reuse(node, current, visit) {
      for (let index = 0; index < node.keys.length; index += 1) {
        const key = node.keys[index]
        const descriptor = Object.getOwnPropertyDescriptor(current, key)
        if (descriptor === undefined) return false
        // An own accessor observed in this call stays when the value it returned is the
        // resolved child itself, compared without calling the getter again; a draft handle it
        // returned does not match, so that object is rebuilt with data.
        if (!isDataDescriptor(descriptor)) {
          if (
            ((node.attributes?.[index] ?? 0) & OBSERVED_ACCESSOR) === 0 ||
            !visit(node.observed?.[index], node.edges[index])
          )
            return false
          continue
        }
        if (!visit(Reflect.get(current, key), node.edges[index])) return false
      }
      const keys = ownKeys(current)
      return (
        keys.length === node.keys.length && keys.every((key, index) => key === node.keys[index])
      )
    },
  } satisfies ImmutablePolicy<ObjectLayout>['immutable']),
  freshWrite(node, target, index, resolve) {
    const attributes = node.attributes![index]
    const key = node.keys[index]
    const prototype = node.layout.prototype
    // A fresh plain shell has no own keys yet, so assigning a key `Object.prototype` lacks
    // creates the same own descriptor as the explicit definition (`PropertyWrite.constructOn`).
    if (
      (attributes & 7) === 7 &&
      (prototype === Object.prototype || prototype === null) &&
      !(key in Object.prototype)
    ) {
      ;(target as Record<PropertyKey, unknown>)[key] = resolve(node.edges[index])
      return
    }
    defineData(
      target,
      key,
      resolve(node.edges[index]),
      (attributes & 2) !== 0,
      (attributes & 1) !== 0,
      (attributes & 4) !== 0,
    )
  },
  someChild(source, read, test) {
    const keys = ownKeys(source)
    for (let index = 0; index < keys.length; index += 1)
      if (test(read(source, keys[index]))) return true
    return false
  },
}))() satisfies ImmutablePolicy<ObjectLayout>

const objectPolicy = /* @__PURE__ */ (() => ({
  ...objectSnapshot,
  ...objectPublication,
  ...objectImmutable,
}))()

/** Captures the prototype and optional sealed own-property index for plain-object publication. */
export interface ObjectLayout {
  readonly kind: typeof OBJECT_KIND
  readonly prototype: object | null
  /** The source's non-enumerable own keys, which a new property copies. */
  readonly hidden: ReadonlySet<PropertyKey> | undefined
  readonly slots: ReadonlyMap<PropertyKey, Edge> | undefined
}

const objectDraftRules: PropertyDraftRules<typeof OBJECT_KIND> = {
  admits: yes,
  kind: OBJECT_KIND,
  methods: undefined,
  capture: () => undefined,
  configurable: () => true,
  initialize: () => undefined,
  target: (base, prototype) =>
    Object.create(
      prototype === undefined ? (Object.getPrototypeOf(base) as object | null) : prototype,
    ) as object,
  write: (_state, copy, key, value) => writeDataSlot(copy, key, value),
}

export const objectDraft = /* @__PURE__ */ freeze({
  tag: 'structural',
  handle: (state, prototype) => createPropertyHandle(state, prototype),
  state: (base, context) => new PropertyDraftState(base, context, objectDraftRules),
}) satisfies DraftStrategy<PropertyDraftState<typeof OBJECT_KIND>>

const objectRecognition = /* @__PURE__ */ freeze({
  tag: 'fallback',
}) satisfies Recognition

export const objectType = /* @__PURE__ */ defineType<
  ObjectLayout,
  PropertyDraftState<typeof OBJECT_KIND>
>({
  draft: objectDraft,
  kind: OBJECT_KIND,
  name: 'object',
  policy: objectPolicy,
  recognition: objectRecognition,
})
