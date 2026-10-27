import { atomValue, isNode } from '../../graph/edge'
import { isObject } from '../../object-property'
import type { Compare, Edge, NativePolicy, Primitive } from '../../types'

const identity = (edge: Edge): unknown => (isNode(edge) ? edge : atomValue(edge))

/**
 * Normalizes native collection keys while retaining first insertion order and last values.
 *
 * @remarks
 * Canonical node references are identity keys. Native Map supplies atom SameValueZero behavior;
 * this is a runtime premise, not an ECMAScript equality model in Lean.
 */
export const normalize = (edges: readonly Edge[], width: number): Edge[] => {
  const entries = new Map<unknown, number>()
  for (let index = 0; index < edges.length; index += width)
    entries.set(identity(edges[index]), index)
  const result: Edge[] = []
  for (const entry of entries) {
    const key = entry[0]
    const index = entry[1]
    const first = edges[index]
    // A primitive key is the Map's canonical one (+0 for -0); an object atom is its own key.
    // Capture delivers whole entries, so every slot of the entry exists.
    result.push(isNode(first) || isObject(first) ? first : (key as Primitive))
    for (let slot = 1; slot < width; slot += 1) result.push(edges[index + slot])
  }
  return result
}

// Map keys and Set members are equal as the collections compare them (SameValueZero).
const sameKey = (left: unknown, right: unknown): boolean =>
  left === right || (Number.isNaN(left) && Number.isNaN(right))

/** How a collection's entries are read and written, with the built-in methods. */
export interface CollectionAccess {
  /** Opens an iterator of the entries, as `[key, value]` pairs or members, that `step` advances. */
  open: (current: object) => object
  step: (iterator: object) => IteratorResult<unknown>
  /** Writes one entry: a `Map` key and value, or a `Set` member (`value` unused). */
  put: (current: object, key: unknown, value: unknown) => void
  remove: (current: object, key: unknown) => void
  size: (current: object) => number
  /** The edges an entry spans: a `Map` key and value, or a `Set` member. */
  readonly width: number
  /** Slot `slot` of an entry that `step` returned, undefined past the last entry. */
  read: (entry: unknown, slot: number) => unknown
}

/**
 * Whether `current` holds exactly the entries that `edges` lists, in order, with `visit` accepting
 * each slot. The built-in iterator lists the entries, so nothing observes the walk.
 */
export function entriesMatch(
  access: CollectionAccess,
  edges: readonly Edge[],
  current: object,
  visit: Compare,
): boolean {
  const width = access.width
  if (access.size(current) * width !== edges.length) return false
  const entries = access.open(current)
  for (let index = 0; index < edges.length; index += width) {
    const entry: unknown = access.step(entries).value
    for (let slot = 0; slot < width; slot += 1)
      if (!visit(access.read(entry, slot), edges[index + slot])) return false
  }
  return true
}

/**
 * Builds the ordered collection walker of a Map or Set publication facet.
 *
 * @remarks
 * A collection is read and written with `access`, so no override that a subclass or the instance
 * holds runs.
 *
 * @param access - Type-owned entry shape and the built-in access to entries.
 */
export function collectionSurface(
  access: CollectionAccess,
): Pick<NativePolicy, 'aligned' | 'matches' | 'publish'> {
  const width = access.width
  // The current entries, flattened as the edges are: key then value for a Map, member for a Set.
  const entriesOf = (current: object): unknown[] => {
    const present: unknown[] = []
    const entries = access.open(current)
    for (let step = access.step(entries); step.done !== true; step = access.step(entries))
      for (let slot = 0; slot < width; slot += 1) present.push(access.read(step.value, slot))
    return present
  }
  // Puts `value` at `key` unless the entry already holds it; whether it wrote.
  const put = (current: object, key: unknown, held: unknown, value: unknown): boolean => {
    if (Object.is(held, value)) return false
    access.put(current, key, value)
    return true
  }
  return {
    aligned(node, current, visit) {
      const edges = node.edges
      const entries = current === undefined ? undefined : access.open(current)
      for (let index = 0; index < edges.length; index += width) {
        const entry: unknown = entries === undefined ? undefined : access.step(entries).value
        for (let slot = 0; slot < width; slot += 1) {
          const edge = edges[index + slot]
          if (isNode(edge)) visit(access.read(entry, slot), edge)
        }
      }
    },
    matches: (node, current, visit) => entriesMatch(access, node.edges, current, visit),
    publish(node, current, resolve, _owner, note) {
      const edges = node.edges
      const present = entriesOf(current)
      const count = present.length / width
      const wanted = edges.length / width
      // The current entries that form, in order, the longest prefix of next's entries keep their
      // place, a Map entry among them taking its next value; every other current entry is
      // deleted, and the next entries past that prefix are added in order. Deleting and adding
      // an entry appends it, so this reaches next's order with the fewest moves, writing what
      // the reference writes (CollectionPlan.publish_result, publish_retained,
      // publish_entryWrites; Spec.Reconcile.retainPrefix_longest).
      let unchanged = true
      let position = 0
      for (let index = 0; index < count; index += 1) {
        const key = present[index * width]
        if (position < wanted && sameKey(key, resolve(edges[position * width]))) {
          if (
            width === 2 &&
            put(current, key, present[index * 2 + 1], resolve(edges[position * 2 + 1]))
          )
            unchanged = false
          position += 1
        } else {
          access.remove(current, key)
          unchanged = false
        }
      }
      for (; position < wanted; position += 1) {
        access.put(
          current,
          resolve(edges[position * width]),
          width === 2 ? resolve(edges[position * width + 1]) : undefined,
        )
        unchanged = false
      }
      // Unchanged exactly when every entry was in place with its value: readback would accept
      // (CollectionPlan.unchanged_iff, WriteFreeReadback.collection_writeFree_matches).
      if (note !== undefined) note.unchanged = unchanged
      return true
    },
  }
}
