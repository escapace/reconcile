import { freeze, independentBindings, yes } from './shared/empty'
import { ordinaryExposure } from './shared/empty'
import { noValue } from './shared/empty'
import type {
  CapturePolicy,
  ConstructionPolicy,
  SnapshotPolicy,
  PublicationPolicy,
  ImmutablePolicy,
  DraftStrategy,
  Recognition,
} from '../types'
import { isObject, ownKeys } from '../object-property'
import { setOwnProperty } from '../set-own-property'
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
  publishProperty,
} from './shared/property-publication'

import { alignedProperties, backedProperty } from './shared/properties'

/** Stable global identity owned by the object module. */
export const OBJECT_KIND = Symbol.for('@escapace/reconcile/object')

const objectSurface: PropertySurface<ObjectLayout> = {
  compatible: yes,
  keys: ownKeys,
  ordered: true,
  slots: (node) => node.layout.slots ?? propertySlots(node),
}

const objectCapture = {
  construction: noValue,
  observe(value, begin, edge) {
    const prototype = Object.getPrototypeOf(value) as object | null
    const names = Object.getOwnPropertyNames(value)
    begin({ kind: OBJECT_KIND, prototype })
    // Symbols are listed after string getters run, so keys those getters add are captured.
    for (const key of names) edge(Reflect.get(value, key) as unknown, key)
    for (const key of Object.getOwnPropertySymbols(value))
      edge(Reflect.get(value, key) as unknown, key)
  },
} satisfies CapturePolicy<ObjectLayout>

const objectConstruction = {
  bindings: independentBindings,
  allocate: (node) => Object.create(node.layout.prototype) as object,
} satisfies ConstructionPolicy<ObjectLayout>

export const objectSnapshot = /* @__PURE__ */ (() =>
  /* @__PURE__ */ freeze({
    ...objectCapture,
    snapshot(layout, resolve, writer) {
      const target = Object.create(layout.prototype) as Record<PropertyKey, unknown>
      writer.initialize(layout, target, (edge, key) => setOwnProperty(target, key!, resolve(edge)))
    },
  }))() satisfies SnapshotPolicy<ObjectLayout>

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
    publish(node, target, image) {
      const properties = objectSurface.slots(node)
      const keys = node.keys
      const previous = ownKeys(target)
      const order = alignedPrefix(previous, keys) ? undefined : new PropertyOrder(properties)
      for (const key of previous) {
        const retained = order?.keep(key)
        if (
          !properties.has(key) ||
          (retained === false &&
            Object.getOwnPropertyDescriptor(target, key)?.configurable !== false)
        ) {
          if (!Reflect.deleteProperty(target, key)) return false
        }
      }
      for (const key of keys)
        if (!publishProperty(target, key, image(properties.get(key)!))) return false
      return true
    },
    requirements: (node, current) => propertyRequirements(node, current, objectSurface),
    // The building node and its layout are private to this capture; seal indexes them in place.
    seal(node) {
      ;(node.layout as { slots?: ReadonlyMap<PropertyKey, Edge> }).slots = propertySlots(node)
      return node
    },
  }))() satisfies PublicationPolicy<ObjectLayout>

// Packs a data descriptor's configurable, enumerable and writable flags into bits 1, 2 and 4.
const attributeBits = (descriptor: PropertyDescriptor): number =>
  (descriptor.configurable === true ? 1 : 0) |
  (descriptor.enumerable === true ? 2 : 0) |
  (descriptor.writable === true ? 4 : 0)

export const objectImmutable = /* @__PURE__ */ (() => ({
  ...objectConstruction,
  immutable: /* @__PURE__ */ freeze({
    tag: 'structural',
    observeDraft(source, begin, edge, { base, properties, read }) {
      const prototype =
        properties === undefined
          ? (Object.getPrototypeOf(source) as object | null)
          : properties.sourcePrototype()
      begin({ kind: OBJECT_KIND, prototype })
      const keys = properties === undefined ? ownKeys(source) : properties.keys(source)
      for (const key of keys) {
        const descriptor =
          properties === undefined
            ? Object.getOwnPropertyDescriptor(source, key)
            : properties.ownDescriptor(key)
        const data = descriptor !== undefined && 'value' in descriptor
        const value: unknown = data
          ? properties === undefined
            ? Reflect.get(source, key)
            : properties.read(key)
          : read(source, key)
        const attributes = data ? attributeBits(descriptor) : 7
        edge(value, key, (isObject(value) || !data) && backedProperty(base, key, value), attributes)
      }
    },
    reuse(node, current, visit) {
      for (let index = 0; index < node.keys.length; index += 1) {
        const key = node.keys[index]
        const descriptor = Object.getOwnPropertyDescriptor(current, key)
        if (
          descriptor === undefined ||
          !('value' in descriptor) ||
          !visit(Reflect.get(current, key), node.edges[index])
        )
          return false
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
    // A fresh plain shell has no own keys yet and no inherited setter except `__proto__`,
    // so an ordinary data write creates the same own descriptor as the explicit definition.
    if (
      attributes === 7 &&
      key !== '__proto__' &&
      (prototype === Object.prototype || prototype === null)
    ) {
      ;(target as Record<PropertyKey, unknown>)[key] = resolve(node.edges[index])
      return
    }
    Object.defineProperty(target, key, {
      configurable: (attributes & 1) !== 0,
      enumerable: (attributes & 2) !== 0,
      value: resolve(node.edges[index]),
      writable: (attributes & 4) !== 0,
    })
  },
  someChild(source, read, test) {
    for (const key of ownKeys(source)) if (test(read(source, key))) return true
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
  readonly slots?: ReadonlyMap<PropertyKey, Edge>
}

const objectDraftRules: PropertyDraftRules<typeof OBJECT_KIND> = {
  kind: OBJECT_KIND,
  capture: () => undefined,
  configurable: () => true,
  initialize: () => undefined,
  target: (base) => Object.create(Object.getPrototypeOf(base) as object | null) as object,
  write: (_state, copy, key, value) => writeDataSlot(copy, key, value),
}

export const objectDraft = /* @__PURE__ */ freeze({
  tag: 'structural',
  handle: (state) => createPropertyHandle(state),
  state: (base, context) => new PropertyDraftState(base, context, objectDraftRules),
}) satisfies DraftStrategy<PropertyDraftState<typeof OBJECT_KIND>>

export const objectExposure = ordinaryExposure

export const objectRecognition = /* @__PURE__ */ freeze({
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
