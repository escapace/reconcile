import { atomValue, isNode } from '../../graph/edge'
import { arrayIndex, hasOwn, isObject, propertyDescriptor } from '../../object-property'
import type { BoundEdge, CapturedNode, Edge, NodeEdge, PublicationNote } from '../../types'
import {
  defineData,
  denseArray,
  Detached,
  indexIn,
  isDataDescriptor,
} from '../../standard-prototypes'
import { UNREAD } from '../../constants'

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
  // The next current key `through` consumes.
  declare private position: number

  constructor(properties: ReadonlyMap<PropertyKey, Edge>) {
    super()
    this.properties = properties
    this.keys = [...properties.keys()]
    this.cursor = 0
    this.stale = true
    this.retained = 0
    this.symbol = this.keys.findIndex((key) => typeof key === 'symbol')
    this.position = 0
  }

  /** Consumes the current keys in order through `key`, or all of them, and reports whether
   * `key` can stay in place. */
  through(previous: readonly PropertyKey[], key?: PropertyKey): boolean | undefined {
    while (this.position < previous.length) {
      const currentKey = previous[this.position++]
      const retained = this.keep(currentKey)
      if (currentKey === key) return retained
    }
    return undefined
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
  /** The own keys of `current` that publication manages for `node`. */
  readonly keys: (current: object, node: CapturedNode<L>) => PropertyKey[]
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
 * key is listed once and its descriptor read once; a fixed slot's value is taken from what the
 * call already read (`context`), or read once and kept for the publication that follows.
 * @internal
 */
export function canPublishProperties<L extends { readonly kind: symbol }>(
  node: CapturedNode<L>,
  current: object,
  surface: PropertySurface<L>,
  pin: BoundEdge[],
  note?: PublicationNote,
  context: PublicationNote | undefined = note,
): boolean {
  // The slot index is private; a surface that lists desired keys builds it only on demand.
  let index: ReadonlyMap<PropertyKey, Edge> | undefined
  const properties = (): ReadonlyMap<PropertyKey, Edge> => (index ??= surface.slots(node))
  // Desired keys are buffered eagerly; DeferredOrder's cursor model and bridge rely on it.
  const desiredKeys = surface.desired?.(node) ?? [...properties().keys()]
  const previous = surface.keys(current, node)
  // The descriptor read for each current key, kept for the first publication when it asks.
  const descriptors =
    note === undefined ? undefined : denseArray<PropertyDescriptor | undefined>(previous.length)
  if (!surface.compatible(node, current, properties)) return false
  const cursor = fixedSlotsHold(
    node,
    current,
    previous,
    desiredKeys,
    surface.ordered,
    properties,
    pin,
    descriptors,
    context,
  )
  if (
    cursor === false ||
    reachesInheritedAccessor(
      current,
      desiredKeys,
      note?.prototype,
      ownedPrefix(previous, desiredKeys),
    )
  )
    return false
  if (
    !Object.isExtensible(current) &&
    !ownsDesired(current, previous, desiredKeys, cursor, surface.ordered, properties)
  )
    return false
  if (note !== undefined) note.facts = { current, descriptors: descriptors!, keys: previous }
  return true
}

/**
 * Checks the fixed slot of each current key in key order, reading each descriptor once into
 * `descriptors`. A slot that cannot be recreated, a non-configurable one or an accessor written
 * only through its setter, must keep its place in the desired order and, unless it can still
 * change, already hold its expected value; an object pins its node, and two slots may not pin
 * one node to different objects. A configurable accessor that is not desired is deleted.
 *
 * @returns False when a slot cannot hold; otherwise the order cursor, created at the first
 * fixed slot that asks, null when the current keys already begin with the desired order, or
 * undefined when no fixed slot asked. Only private cursor work waits: it consumes current keys
 * only as far as a fixed slot asks, while native descriptors and reads keep their boundaries.
 */
function fixedSlotsHold(
  node: CapturedNode,
  current: object,
  previous: readonly PropertyKey[],
  desiredKeys: readonly PropertyKey[],
  ordered: boolean,
  properties: () => ReadonlyMap<PropertyKey, Edge>,
  pin: BoundEdge[],
  descriptors: Array<PropertyDescriptor | undefined> | undefined,
  context: PublicationNote | undefined,
): false | PropertyOrder | null | undefined {
  // Undecided until the first fixed slot asks; null once the keys already begin in order.
  let order: PropertyOrder | null | undefined
  let pinned: Map<number, object> | undefined
  for (let position = 0; position < previous.length; position += 1) {
    const key = previous[position]
    const descriptor = Object.getOwnPropertyDescriptor(current, key)!
    if (descriptors !== undefined) descriptors[position] = descriptor
    if (descriptor.configurable !== false && isDataDescriptor(descriptor)) continue
    if (order === undefined && ordered) order = orderFor(previous, desiredKeys, properties) ?? null
    const retained = order?.through(previous, key)
    const held = fixedSlot(node, current, key, descriptor, retained, properties(), context)
    if (held === true) continue
    if (
      held === false ||
      !pinNode(
        pin,
        (pinned ??= new Map<number, object>()),
        (properties().get(key) as NodeEdge).node,
        held,
      )
    )
      return false
  }
  return order
}

// Pins `node` to `identity`; false when an earlier slot pinned it to another object.
function pinNode(
  pin: BoundEdge[],
  pinned: Map<number, object>,
  node: number,
  identity: object,
): boolean {
  pin.push({ identity, node })
  if (pinned.has(node) && pinned.get(node) !== identity) return false
  pinned.set(node, identity)
  return true
}

/**
 * Whether a non-extensible `current` already owns every desired key, in an order its key cursor
 * can reach. The rest of the current keys are consumed only here, once no write can change them.
 */
function ownsDesired(
  current: object,
  previous: readonly PropertyKey[],
  desiredKeys: readonly PropertyKey[],
  cursor: PropertyOrder | null | undefined,
  ordered: boolean,
  properties: () => ReadonlyMap<PropertyKey, Edge>,
): boolean {
  const order =
    cursor === undefined && ordered
      ? orderFor(previous, desiredKeys, properties)
      : (cursor ?? undefined)
  order?.through(previous)
  if (order !== undefined) return order.retained === desiredKeys.length
  for (let index = 0; index < desiredKeys.length; index += 1)
    if (!hasOwn(current, desiredKeys[index])) return false
  return true
}

/**
 * Whether a fixed slot holds: false when it cannot, true when it needs nothing more, or the
 * object it holds, which pins the expected node. A slot `next` lacks may stay only when it is
 * configurable; one out of order cannot stay; one that can still change holds; otherwise it
 * must already hold the expected value.
 */
function fixedSlot(
  node: CapturedNode,
  current: object,
  key: PropertyKey,
  descriptor: PropertyDescriptor,
  retained: boolean | undefined,
  properties: ReadonlyMap<PropertyKey, Edge>,
  context: PublicationNote | undefined,
): boolean | object {
  if (!properties.has(key)) return descriptor.configurable !== false
  if (retained === false) return false
  const expected = properties.get(key)!
  if (isDataDescriptor(descriptor) ? descriptor.writable !== false : descriptor.set !== undefined)
    return true
  const actual = heldValue(node, current, key, context)
  if (isNode(expected) && isObject(actual)) return actual
  return !isNode(expected) && Object.is(atomValue(expected), actual)
}

/**
 * The value of a fixed slot: what the call already read at its edge (`context.reads`), what an
 * earlier preflight of this publication read, or one read now, kept in `context.held` so that
 * publication decides from it (Property.WriteFreeReadback.publishPre, publishSeen).
 */
function heldValue(
  node: CapturedNode,
  current: object,
  key: PropertyKey,
  context: PublicationNote | undefined,
): unknown {
  const reads = context?.reads
  const edge = reads === undefined ? -1 : indexIn(node.keys, key)
  if (edge !== -1 && edge < reads!.length && reads![edge] !== UNREAD) return reads![edge]
  let held = context?.held?.get(current)
  if (held?.has(key) === true) return held.get(key)
  const value = Reflect.get(current, key) as unknown
  if (context !== undefined) {
    if (held === undefined) (context.held ??= new Map()).set(current, (held = new Map()))
    held.set(key, value)
  }
  return value
}

/**
 * What the call already read at edge `index`, which holds `key`, of the object being published:
 * capture's or a previous readback's read, else what a preflight of this publication read at that
 * fixed slot (`held`), else `UNREAD`. A key publication deleted first (`removed`) holds no read.
 */
export function priorRead(
  reads: readonly unknown[] | undefined,
  index: number,
  held: ReadonlyMap<PropertyKey, unknown> | undefined,
  key: PropertyKey,
  removed?: readonly PropertyKey[],
): unknown {
  if (removed?.includes(key) === true) return UNREAD
  const read = reads !== undefined && index < reads.length ? reads[index] : UNREAD
  return read === UNREAD && held?.has(key) === true ? held.get(key) : read
}

// The order cursor for `previous`, or undefined when it already begins with the desired order.
const orderFor = (
  previous: readonly PropertyKey[],
  desiredKeys: readonly PropertyKey[],
  properties: () => ReadonlyMap<PropertyKey, Edge>,
): PropertyOrder | undefined =>
  alignedPrefix(previous, desiredKeys) ? undefined : new PropertyOrder(properties())

// The count of current own keys when they begin with the desired order, otherwise -1.
const ownedPrefix = (
  previous: readonly PropertyKey[],
  desiredKeys: readonly PropertyKey[],
): number => (alignedPrefix(previous, desiredKeys) ? previous.length : -1)

/**
 * Whether assigning a desired key that `current` lacks would reach an accessor on its prototype
 * chain. `__proto__` is defined, never assigned.
 *
 * @remarks
 * When the current own keys, listed before any write, begin with the desired order, `owned` is
 * their count: desired key `i` is own exactly when `i < owned` (PropertyOrder.reaches_aligned),
 * so only the later keys are asked, and never whether they are own. Otherwise it is -1.
 */
function reachesInheritedAccessor(
  current: object,
  desiredKeys: readonly PropertyKey[],
  prototype: object | null | undefined,
  owned: number,
): boolean {
  if (owned >= desiredKeys.length) return false
  // Capture's read of the prototype serves here when it read one.
  const first =
    prototype === undefined ? (Object.getPrototypeOf(current) as object | null) : prototype
  if (first === null) return false
  for (let index = owned < 0 ? 0 : owned; index < desiredKeys.length; index += 1) {
    const key = desiredKeys[index]
    if (
      key !== '__proto__' &&
      (owned >= 0 ? accessorFrom(first, key) : lacksAccessor(current, first, key))
    )
      return true
  }
  return false
}

/**
 * Whether `current` lacks `key` and `first` reaches an accessor for it. On a standard prototype
 * only a key it holds can reach an accessor; the prototype is asked first, so `current` is asked
 * only for such a key, which no unmodified prototype makes. Elsewhere `current` is asked first.
 */
function lacksAccessor(current: object, first: object, key: PropertyKey): boolean {
  return first === Object.prototype || first === Array.prototype
    ? accessorFrom(first, key) && !hasOwn(current, key)
    : !hasOwn(current, key) && accessorFrom(first, key)
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
  return writeProperty(target, key, value, present)
}

// The write of `publishProperty`, once a read has shown that the key needs one.
function writeProperty(target: object, key: PropertyKey, value: unknown, present: boolean): number {
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

/**
 * `publishKnown` with a value the call already read of this key (`read`): the one aligned capture,
 * candidate discovery or a preflight read before the first write, or the one a retried plan's
 * previous readback saw.
 * It decides whether the key needs a write, without reading it again, and the descriptor, or else
 * the live slot, gives the presence and attributes the write uses
 * (Property.WriteFreeReadback.publishPre, publishSeen); with stable reads that is
 * `publishProperty`'s decision (publishPre_eq, publishSeen_eq). After an earlier write the read can
 * be stale, which the readback that follows any write catches (accepts_readsAs,
 * acceptsRetry_readsAs).
 */
export function publishRead(
  target: object,
  key: PropertyKey,
  value: unknown,
  descriptor: PropertyDescriptor | undefined,
  read: unknown,
): number {
  if (Object.is(read, value)) return UNCHANGED
  if (descriptor === undefined) return writeProperty(target, key, value, hasOwn(target, key))
  return wrote(
    isDataDescriptor(descriptor)
      ? assignData(target, key, value, descriptor)
      : Reflect.set(target, key, value),
  )
}

// Assignment lets a reactive proxy observe the write; a definition follows when assignment left
// no own property, or when it refused a key the object holds read-only. Any other refusal, such as
// a proxy's `set` trap rejecting the value, stands (PropertyWrite.assignStrict_eq).
function assignData(
  target: object,
  key: PropertyKey,
  value: unknown,
  descriptor: PropertyDescriptor | undefined,
): boolean {
  if (Reflect.set(target, key, value)) {
    if (hasOwn(target, key)) return true
  } else if (
    (descriptor ?? propertyDescriptor(Object.getPrototypeOf(target) as object | null, key))
      ?.writable !== false
  )
    return false
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
  context: PublicationNote | undefined = note,
): readonly BoundEdge[] | undefined {
  const required: BoundEdge[] = []
  return canPublishProperties(node, candidate, surface, required, note, context)
    ? required
    : undefined
}
