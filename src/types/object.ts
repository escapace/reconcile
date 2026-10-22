import { OBJECT_KIND } from '../constants'
import { snapshotValue, type SnapshotReceiver } from '../graph/edge'
import { freeze, independentBindings, yes } from './shared/empty'
import { ordinaryExposure } from './shared/empty'
import { noValue } from './shared/empty'
import type {
  CapturedNode,
  CapturePolicy,
  ConstructionPolicy,
  SnapshotPolicy,
  PublicationPolicy,
  ImmutablePolicy,
  DraftStrategy,
  Recognition,
} from '../types'
import { hasOwn, hiddenNames, isEnumerable, isObject, ownKeys } from '../object-property'
import { setOwnProperty, standardPrototype } from '../set-own-property'
import type { Edge } from '../types'
import { defineType } from './registry'
import type { PropertyDraftRules } from './shared/draft-properties'
import { createPropertyHandle, PropertyDraftState, writeDataSlot } from './shared/draft-properties'
import type { PropertySurface } from './shared/property-publication'
import {
  alignedPrefix,
  PropertyOrder,
  propertyRequirements,
  propertySlots,
  publishKnown,
  REFUSED,
  UNCHANGED,
  WROTE,
} from './shared/property-publication'

import { alignedProperties, backedProperty } from './shared/properties'
import { defineData, hide, isDataDescriptor } from '../standard-prototypes'

/** Stable global identity owned by the object module. */
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
    // Symbols are listed after string getters run, so keys those getters add are captured.
    for (const key of names) edge(Reflect.get(value, key) as unknown, key)
    for (const key of Object.getOwnPropertySymbols(value)) {
      edge(Reflect.get(value, key) as unknown, key)
      if (!isEnumerable(value, key))
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

export const objectSnapshot = /* @__PURE__ */ (() =>
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
 * enumerability, so a hidden one stays hidden; an existing one keeps its own attributes.
 * `known` holds the preflight's descriptor for each requested key the target already had in
 * the same position. Returns `REFUSED`, `WROTE`, or `UNCHANGED` when no key was written. */
function writeProperties(
  node: CapturedNode<ObjectLayout>,
  target: object,
  image: (edge: Edge) => unknown,
  known: ReadonlyArray<PropertyDescriptor | undefined> | undefined,
): number {
  const hidden = node.layout.hidden
  let result = UNCHANGED
  for (let index = 0; index < node.keys.length; index += 1) {
    const key = node.keys[index]
    const descriptor = known !== undefined && index < known.length ? known[index] : undefined
    const added = descriptor === undefined && hidden?.has(key) === true && !hasOwn(target, key)
    const written = publishKnown(target, key, image(node.edges[index]), descriptor)
    if (written === REFUSED) return REFUSED
    if (written === WROTE) result = WROTE
    if (added && !hide(target, key)) return REFUSED
  }
  return result
}

/** Deletes the current keys the requested order does not keep: past the requested count in the
 * aligned order, otherwise unrequested or configurable and out of order. Returns `REFUSED`,
 * `WROTE` when it deleted a key, or `UNCHANGED`. */
function deleteUnrequested(
  target: object,
  previous: readonly PropertyKey[],
  requested: number,
  properties: ReadonlyMap<PropertyKey, Edge> | undefined,
): number {
  const order = properties === undefined ? undefined : new PropertyOrder(properties)
  let result = UNCHANGED
  for (let position = 0; position < previous.length; position += 1) {
    const key = previous[position]
    const retained = order?.keep(key)
    if (
      !(properties === undefined ? position < requested : properties.has(key)) ||
      (retained === false && Object.getOwnPropertyDescriptor(target, key)?.configurable !== false)
    ) {
      if (!Reflect.deleteProperty(target, key)) return REFUSED
      result = WROTE
    }
  }
  return result
}

export const objectPublication = /* @__PURE__ */ (() =>
  /* @__PURE__ */ freeze({
    ...objectCapture,
    ...objectConstruction,
    aligned: alignedProperties,
    compatible: yes,
    matches(node, current, visit) {
      const keys = ownKeys(current)
      if (keys.length !== node.keys.length) return false
      for (let index = 0; index < keys.length; index += 1) {
        const key = node.keys[index]
        if (keys[index] !== key || !visit(Reflect.get(current, key), node.edges[index]))
          return false
      }
      return true
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
      const deleted = deleteUnrequested(target, previous, keys.length, properties)
      if (deleted === REFUSED) return false
      // In the aligned order, descriptor i belongs to requested key i.
      const written = writeProperties(
        node,
        target,
        image,
        properties === undefined ? facts?.descriptors : undefined,
      )
      // Aligned, nothing deleted and no key written: readback would accept
      // (WriteFreeReadback.object_writeFree_matches).
      if (note !== undefined)
        note.unchanged = written === UNCHANGED && properties === undefined && deleted === UNCHANGED
      return written !== REFUSED
    },
    requirements: (node, current, note) => propertyRequirements(node, current, objectSurface, note),
    // Object slots are indexed on first demand; see objectSurface.
    seal: (node) => node,
  }))() satisfies PublicationPolicy<ObjectLayout>

// Packs a data descriptor's configurable, enumerable and writable flags into bits 1, 2 and 4.
/** Data attributes of a getter's value in a rebuilt object, with a bit marking the accessor. */
export const OBSERVED_ACCESSOR = 15

const attributeBits = (descriptor: PropertyDescriptor): number =>
  (descriptor.configurable === true ? 1 : 0) |
  (descriptor.enumerable === true ? 2 : 0) |
  (descriptor.writable === true ? 4 : 0)

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
      for (const key of keys) {
        const descriptor =
          properties === undefined
            ? Object.getOwnPropertyDescriptor(source, key)
            : properties.ownDescriptor(key)
        const data = descriptor !== undefined && isDataDescriptor(descriptor)
        const value: unknown = data
          ? properties === undefined
            ? Reflect.get(source, key)
            : properties.read(key)
          : observer.read(source, key)
        const attributes = data ? attributeBits(descriptor) : OBSERVED_ACCESSOR
        observer.edge(
          value,
          key,
          (isObject(value) || !data) && backedProperty(base, key, value),
          attributes,
        )
      }
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
            node.attributes?.[index] !== OBSERVED_ACCESSOR ||
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

export const objectExposure = ordinaryExposure

const objectRecognition = /* @__PURE__ */ freeze({
  tag: 'fallback',
}) satisfies Recognition

export const objectType = /* @__PURE__ */ defineType<
  ObjectLayout,
  PropertyDraftState<typeof OBJECT_KIND>
>({
  draft: objectDraft,
  exposure: objectExposure,
  kind: OBJECT_KIND,
  name: 'object',
  policy: objectPolicy,
  recognition: objectRecognition,
})
