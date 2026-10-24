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
    result.push(isNode(first) || isObject(first) ? first : (key as Primitive))
    for (let slot = 1; slot < width && index + slot < edges.length; slot += 1)
      result.push(edges[index + slot])
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
}

/**
 * Builds the ordered collection walker of a Map or Set publication facet.
 *
 * @remarks
 * A collection is read and written with `builtin`, so no override that a subclass or the instance
 * holds runs.
 *
 * @param operations - Type-owned entry shape and the access to entries.
 */
export function collectionSurface(operations: {
  builtin: CollectionAccess
  readonly width: number
  read: (entry: unknown, slot: number, strict: boolean) => unknown
}): Pick<NativePolicy, 'aligned' | 'matches' | 'publish'> {
  const { builtin: access, width } = operations
  const walk = (
    node: readonly Edge[],
    current: object | undefined,
    visit: Compare,
    strict: boolean,
  ): boolean => {
    const previous = current === undefined ? undefined : access.open(current)
    for (let index = 0; index < node.length; index += width) {
      const entry: unknown = previous === undefined ? undefined : access.step(previous).value
      for (let slot = 0; slot < width; slot += 1) {
        if (!strict && !isNode(node[index + slot])) continue
        if (!visit(operations.read(entry, slot, strict), node[index + slot])) return false
      }
    }
    return true
  }
  // The current entries, flattened as the edges are: key then value for a Map, member for a Set.
  const entriesOf = (current: object): unknown[] => {
    const present: unknown[] = []
    const entries = access.open(current)
    for (let step = access.step(entries); step.done !== true; step = access.step(entries))
      for (let slot = 0; slot < width; slot += 1)
        present.push(operations.read(step.value, slot, true))
    return present
  }
  const matches: NativePolicy['matches'] = (node, current, visit) =>
    access.size(current) === node.edges.length / width && walk(node.edges, current, visit, true)
  return {
    matches,
    aligned: (node, current, visit) => {
      walk(
        node.edges,
        current,
        (actual, edge) => {
          if (isNode(edge)) visit(actual, edge)
          return true
        },
        false,
      )
    },
    publish(node, current, resolve, _owner, note) {
      const edges = node.edges
      const present = entriesOf(current)
      const count = present.length / width
      const wanted = edges.length / width
      // Entries match by position. Up to the first position whose key or member differs, each
      // stays in place and a Map entry takes its next value; from there on the current entries
      // are deleted and the next ones appended, which is the only way to reach their order
      // (CollectionPlan.plan_eq).
      let position = 0
      while (
        position < count &&
        position < wanted &&
        sameKey(present[position * width], resolve(edges[position * width]))
      )
        position += 1
      let unchanged = position === count && position === wanted
      if (width === 2)
        for (let index = 0; index < position; index += 1) {
          const value = resolve(edges[index * 2 + 1])
          if (!Object.is(present[index * 2 + 1], value)) {
            access.put(current, present[index * 2], value)
            unchanged = false
          }
        }
      for (let index = position; index < count; index += 1)
        access.remove(current, present[index * width])
      for (let index = position; index < wanted; index += 1)
        access.put(
          current,
          resolve(edges[index * width]),
          width === 2 ? resolve(edges[index * width + 1]) : undefined,
        )
      // Every entry in place with its value: readback would accept
      // (WriteFreeReadback.collection_writeFree_matches).
      if (note !== undefined) note.unchanged = unchanged
      return true
    },
  }
}
