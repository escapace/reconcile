import { isNode } from '../../graph/edge'
import { arrayIndex, hasOwn, isObject } from '../../object-property'
import type { BoundEdge, CapturedNode, Edge, PublicationNote } from '../../types'
import { defineData, denseArray, Detached, isDataDescriptor } from '../../standard-prototypes'

// Property lookup is a derived index over the sealed graph, never a second graph.
export function propertySlots(node: Pick<CapturedNode, 'edges' | 'keys'>): Map<PropertyKey, Edge> {
  const slots = new Map<PropertyKey, Edge>()
  for (let index = 0; index < node.keys.length; index += 1)
    slots.set(node.keys[index], node.edges[index])
  return slots
}

/** Checks whether the shared prefix already has the requested order, allowing a trailing suffix. */
export function alignedPrefix(
  previous: readonly PropertyKey[],
  desired: readonly unknown[],
): boolean {
  const shared = Math.min(previous.length, desired.length)
  for (let index = 0; index < shared; index += 1)
    if (previous[index] !== desired[index]) return false
  return true
}

/**
 * Tracks which existing plain-object keys can stay in place during ordered publication.
 *
 * @remarks
 * Indices sort numerically; other strings and symbols each retain the longest requested prefix
 * that appears as a subsequence of current keys. Consume current keys once in native order.
 * Preflight and publication use separate instances so no observation is cached across phases.
 */
export class PropertyOrder extends Detached {
  declare private cursor: number
  declare private readonly keys: readonly PropertyKey[]
  // This flag describes only the private desired-key cursor, never a live receiver: the
  // name cursor still has to skip index keys before its next comparison.
  declare private stale: boolean
  /** Counts requested keys that can remain without deletion and reinsertion. */
  declare private readonly properties: ReadonlyMap<PropertyKey, Edge>
  declare retained: number
  declare private symbol: number

  constructor(properties: ReadonlyMap<PropertyKey, Edge>) {
    super()
    this.properties = properties
    this.keys = [...properties.keys()]
    this.cursor = 0
    this.stale = true
    this.retained = 0
    this.symbol = this.keys.findIndex((key) => typeof key === 'symbol')
  }

  /** Advances the order cursors and reports whether this current key can stay in place. */
  keep(key: PropertyKey): boolean {
    const desired = this.keys
    if (arrayIndex(key) !== undefined) {
      if (!this.properties.has(key)) return false
    } else if (typeof key === 'symbol') {
      if (desired[this.symbol] !== key) return false
      this.symbol += 1
    } else {
      if (this.stale) {
        while (this.cursor < desired.length && arrayIndex(desired[this.cursor]) !== undefined)
          this.cursor += 1
        this.stale = false
      }
      if (desired[this.cursor] !== key) return false
      this.cursor += 1
      this.stale = true
    }
    this.retained += 1
    return true
  }
}

/** Supplies type-owned shape, ordering and slot rules to shared property publication. */
export interface PropertySurface<L extends { readonly kind: symbol }> {
  readonly ordered: boolean
  readonly compatible: (
    node: CapturedNode<L>,
    current: object,
    properties: () => ReadonlyMap<PropertyKey, Edge>,
  ) => boolean
  /** The requested keys in order, equal to the slot index's keys; defaults to listing them. */
  readonly desired: ((node: CapturedNode<L>) => readonly PropertyKey[]) | undefined
  readonly keys: (current: object) => PropertyKey[]
  readonly slots: (node: CapturedNode<L>) => ReadonlyMap<PropertyKey, Edge>
}

/**
 * Checks a property candidate's fixed properties, extensibility and key order before writes
 * begin, and compiles its fixed object slots into identity requirements in `pin`.
 *
 * @remarks
 * This is the preflight: candidate discovery runs it once per candidate, and the engine reruns it
 * only after the call's own writes. It rules out representation failures but cannot predict
 * setter or proxy behavior, so publication and readback still verify the result. Each candidate
 * key is listed once and its descriptor read once; each fixed slot is read once.
 * @internal
 */
export function canPublishProperties<L extends { readonly kind: symbol }>(
  node: CapturedNode<L>,
  current: object,
  surface: PropertySurface<L>,
  pin: BoundEdge[],
  note?: PublicationNote,
): boolean {
  // The slot index is private; a surface that lists desired keys builds it only on demand.
  let index: ReadonlyMap<PropertyKey, Edge> | undefined
  const properties = (): ReadonlyMap<PropertyKey, Edge> => (index ??= surface.slots(node))
  // Desired keys are buffered eagerly; DeferredOrder's cursor model and bridge rely on it.
  const desiredKeys = surface.desired?.(node) ?? [...properties().keys()]
  const previous = surface.keys(current)
  let needsOrder = surface.ordered
  let order: PropertyOrder | undefined
  let position = 0
  let pinned: Map<number, object> | undefined
  // The descriptor read for each current key, kept for the first publication when it asks.
  const descriptors =
    note === undefined ? undefined : denseArray<PropertyDescriptor | undefined>(previous.length)
  // Only private cursor work waits. Native descriptors and reads keep their boundaries.
  const retainThrough = (key?: PropertyKey): boolean | undefined => {
    if (order === undefined) {
      if (alignedPrefix(previous, desiredKeys)) {
        needsOrder = false
        return undefined
      }
      order = new PropertyOrder(properties())
    }
    while (position < previous.length) {
      const currentKey = previous[position++]
      const retained = order.keep(currentKey)
      if (currentKey === key) return retained
    }
    return undefined
  }
  // A slot that cannot be recreated, a non-configurable one or an accessor written only through
  // its setter, must keep its place in the desired order and, unless it can still change,
  // already hold its expected value; an object pins its node, and two slots may not pin one node
  // to different objects. A configurable accessor that is not desired is deleted.
  const holdsFixed = (key: PropertyKey, position: number): boolean => {
    const descriptor = Object.getOwnPropertyDescriptor(current, key)!
    if (descriptors !== undefined) descriptors[position] = descriptor
    const accessor = !isDataDescriptor(descriptor)
    if (descriptor.configurable !== false && !accessor) return true
    const retained = needsOrder ? retainThrough(key) : undefined
    if (!properties().has(key)) return descriptor.configurable !== false
    if (retained === false) return false
    const expected = properties().get(key)!
    if (isDataDescriptor(descriptor) ? descriptor.writable !== false : descriptor.set !== undefined)
      return true
    const actual = Reflect.get(current, key) as unknown
    if (!isNode(expected) || !isObject(actual))
      return !isNode(expected) && Object.is(expected.value, actual)
    pin.push({ identity: actual, node: expected.node })
    pinned ??= new Map()
    if (pinned.has(expected.node) && pinned.get(expected.node) !== actual) return false
    pinned.set(expected.node, actual)
    return true
  }
  if (
    !surface.compatible(node, current, properties) ||
    !previous.every(holdsFixed) ||
    reachesInheritedAccessor(current, desiredKeys)
  )
    return false
  if (!Object.isExtensible(current)) {
    if (needsOrder) retainThrough()
    if (order !== undefined) return order.retained === desiredKeys.length
    for (let index = 0; index < desiredKeys.length; index += 1)
      if (!hasOwn(current, desiredKeys[index])) return false
  }
  if (note !== undefined) note.facts = { current, descriptors: descriptors!, keys: previous }
  return true
}

/**
 * Whether assigning a desired key that `current` lacks would reach an accessor on its prototype
 * chain. `__proto__` is defined, never assigned.
 */
function reachesInheritedAccessor(current: object, desiredKeys: readonly PropertyKey[]): boolean {
  const first = Object.getPrototypeOf(current) as object | null
  if (first === null) return false
  // On a standard prototype only a key it holds can reach an accessor; the prototype is asked
  // first, so `current` is asked only for such a key, which no unmodified prototype makes.
  if (first === Object.prototype || first === Array.prototype) {
    for (let index = 0; index < desiredKeys.length; index += 1) {
      const key = desiredKeys[index]
      if (key !== '__proto__' && accessorFrom(first, key) && !hasOwn(current, key)) return true
    }
    return false
  }
  for (let index = 0; index < desiredKeys.length; index += 1) {
    const key = desiredKeys[index]
    if (key !== '__proto__' && !hasOwn(current, key) && accessorFrom(first, key)) return true
  }
  return false
}

/**
 * Whether the first descriptor for `key` from `prototype` up is an accessor.
 *
 * @remarks
 * `Array.prototype` and `Object.prototype` are read only for a key they hold, whatever code added
 * it: `in` answers for both, since one inherits from the other.
 */
function accessorFrom(prototype: object | null, key: PropertyKey): boolean {
  for (let current = prototype; current !== null;) {
    if ((current === Object.prototype || current === Array.prototype) && !(key in current))
      return false
    const descriptor = Object.getOwnPropertyDescriptor(current, key)
    if (descriptor !== undefined) return !isDataDescriptor(descriptor)
    current = Object.getPrototypeOf(current) as object | null
  }
  return false
}

/** `publishProperty` failed: a native operation refused the write. */
export const REFUSED = 0
/** `publishProperty` wrote. */
export const WROTE = 1
/** `publishProperty` wrote nothing: the key was own and read as the value. */
export const UNCHANGED = 2

/**
 * Writes one requested own value by assignment, so own setters run and accessors are kept.
 *
 * @remarks
 * Unchanged values require no write. An own accessor is assigned, never redefined. A missing
 * key whose assignment would reach an accessor, including `__proto__`, becomes an own data
 * property. Other writes assign before defining an own property, so a reactive proxy observes
 * them. `PropertyWrite.publish` is this decision.
 *
 * @returns `REFUSED` when a native operation refused the write, `UNCHANGED` when nothing was
 * written and otherwise `WROTE`. Contents require separate readback.
 */
export function publishProperty(target: object, key: PropertyKey, value: unknown): number {
  // An unchanged own value needs no descriptor: presence and one read decide it.
  const present = hasOwn(target, key)
  if (present && Object.is(Reflect.get(target, key), value)) return UNCHANGED
  const descriptor = present ? Object.getOwnPropertyDescriptor(target, key) : undefined
  // A missing key whose assignment would reach an accessor is defined, so no setter runs; for an
  // object `reconcile` keeps, the preflight has already rejected that case.
  if (descriptor === undefined)
    return wrote(
      key === '__proto__' || accessorFrom(Object.getPrototypeOf(target) as object | null, key)
        ? defineData(target, key, value)
        : assignData(target, key, value, undefined),
    )
  // An own accessor is assigned, so its setter runs; it is never redefined.
  return wrote(
    isDataDescriptor(descriptor)
      ? assignData(target, key, value, descriptor)
      : Reflect.set(target, key, value),
  )
}

const wrote = (accepted: boolean): number => (accepted ? WROTE : REFUSED)

/**
 * `publishProperty` with the descriptor the preflight read for this key, when it read one:
 * presence and attributes come from it and the value is still read live, so the decision is
 * `publishProperty`'s under stable reads (Property.WriteFreeReadback.publishKnown_eq).
 */
export function publishKnown(
  target: object,
  key: PropertyKey,
  value: unknown,
  descriptor: PropertyDescriptor | undefined,
): number {
  if (descriptor === undefined || !isDataDescriptor(descriptor))
    return publishProperty(target, key, value)
  return Object.is(Reflect.get(target, key), value)
    ? UNCHANGED
    : wrote(assignData(target, key, value, descriptor))
}

// Assignment lets a reactive proxy observe the write; a definition follows only when assignment
// left no own property.
function assignData(
  target: object,
  key: PropertyKey,
  value: unknown,
  descriptor: PropertyDescriptor | undefined,
): boolean {
  if (Reflect.set(target, key, value) && hasOwn(target, key)) return true
  return descriptor === undefined
    ? defineData(target, key, value)
    : defineData(
        target,
        key,
        value,
        descriptor.enumerable,
        descriptor.configurable,
        descriptor.writable,
      )
}

// Native fixed slots produce finite identity implications. No target selection occurs here.
export function propertyRequirements<L extends { readonly kind: symbol }>(
  node: CapturedNode<L>,
  candidate: object,
  surface: PropertySurface<L>,
  note?: PublicationNote,
): readonly BoundEdge[] | undefined {
  const required: BoundEdge[] = []
  return canPublishProperties(node, candidate, surface, required, note) ? required : undefined
}
