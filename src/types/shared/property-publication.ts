import { isNode } from '../../graph/edge'
import { arrayIndex, hasOwn, isObject } from '../../object-property'
import type { BoundEdge, CapturedNode, Edge } from '../../types'

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
  desired: Iterable<unknown>,
): boolean {
  let index = 0
  for (const key of desired) {
    if (index === previous.length) break
    if (previous[index++] !== key) return false
  }
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
export class PropertyOrder {
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
    properties: ReadonlyMap<PropertyKey, Edge>,
  ) => boolean
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
  properties: ReadonlyMap<PropertyKey, Edge>,
  pin: BoundEdge[],
): boolean {
  // Desired keys are buffered eagerly; DeferredOrder's cursor model and bridge rely on it.
  const desiredKeys = [...properties.keys()]
  const previous = surface.keys(current)
  let needsOrder = surface.ordered
  let order: PropertyOrder | undefined
  let position = 0
  let pinned: Map<number, object> | undefined
  // Only private cursor work waits. Native descriptors and reads keep their boundaries.
  const retainThrough = (key?: PropertyKey): boolean | undefined => {
    if (order === undefined) {
      if (alignedPrefix(previous, desiredKeys)) {
        needsOrder = false
        return undefined
      }
      order = new PropertyOrder(properties)
    }
    while (position < previous.length) {
      const currentKey = previous[position++]
      const retained = order.keep(currentKey)
      if (currentKey === key) return retained
    }
    return undefined
  }
  // A non-configurable slot must keep its place in the desired order and, unless it can still
  // change, already hold its expected value; an object pins its node, and two slots may not
  // pin one node to different objects.
  const holdsFixed = (key: PropertyKey): boolean => {
    const descriptor = Object.getOwnPropertyDescriptor(current, key)!
    if (descriptor.configurable !== false) return true
    const retained = needsOrder ? retainThrough(key) : undefined
    if (!properties.has(key) || retained === false) return false
    const expected = properties.get(key)!
    if ('value' in descriptor ? descriptor.writable !== false : descriptor.set !== undefined)
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
  if (!surface.compatible(node, current, properties) || !previous.every(holdsFixed)) return false
  if (!Object.isExtensible(current)) {
    if (needsOrder) retainThrough()
    if (order !== undefined) return order.retained === desiredKeys.length
    for (const key of desiredKeys) if (!hasOwn(current, key)) return false
  }
  return true
}

/**
 * Writes one requested own value while preserving applicable descriptor and receiver behavior.
 *
 * @remarks
 * Unchanged values require no write. Configurable accessors become data properties when their
 * value must change. A missing `__proto__` becomes an own data key. Other writes try ordinary
 * assignment before defining an own property, preserving reactive setters where supported.
 *
 * @returns Whether the native operations accepted the write. Contents require separate readback.
 */
export function publishProperty(target: object, key: PropertyKey, value: unknown): boolean {
  // An unchanged own value needs no descriptor: presence and one read decide it.
  const present = hasOwn(target, key)
  if (present && Object.is(Reflect.get(target, key), value)) return true
  const descriptor = present ? Object.getOwnPropertyDescriptor(target, key) : undefined
  if (descriptor !== undefined && !('value' in descriptor) && descriptor.configurable === true)
    return defineData(target, key, value, descriptor.enumerable)
  if (key === '__proto__' && descriptor === undefined) return defineData(target, key, value)
  if (!Reflect.set(target, key, value) || !hasOwn(target, key))
    return descriptor === undefined
      ? defineData(target, key, value)
      : Reflect.defineProperty(target, key, { ...descriptor, value })
  return true
}

const defineData = (target: object, key: PropertyKey, value: unknown, enumerable = true) =>
  Reflect.defineProperty(target, key, { configurable: true, enumerable, value, writable: true })

// Native fixed slots produce finite identity implications. No target selection occurs here.
export function propertyRequirements<L extends { readonly kind: symbol }>(
  node: CapturedNode<L>,
  candidate: object,
  surface: PropertySurface<L>,
): readonly BoundEdge[] | undefined {
  const required: BoundEdge[] = []
  return canPublishProperties(node, candidate, surface, surface.slots(node), required)
    ? required
    : undefined
}
