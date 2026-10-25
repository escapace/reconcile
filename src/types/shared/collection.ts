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
  // Puts `value` at `key` unless the entry already holds it; whether it wrote.
  const put = (current: object, key: unknown, held: unknown, value: unknown): boolean => {
    if (Object.is(held, value)) return false
    access.put(current, key, value)
    return true
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
      // The current entries that form, in order, the longest prefix of next's entries keep their
      // place, a Map entry among them taking its next value; every other current entry is
      // deleted, and the next entries past that prefix are added in order. Deleting and adding
      // an entry appends it, so this reaches next's order with the fewest moves
      // (Spec.Reconcile.collectionWrites, retainPrefix_longest).
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
      // Every entry in place with its value: readback would accept
      // (WriteFreeReadback.collection_writeFree_matches).
      if (note !== undefined) note.unchanged = unchanged
      return true
    },
  }
}
