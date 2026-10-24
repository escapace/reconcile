import { atomValue, isNode } from '../../graph/edge'
import { isObject } from '../../object-property'
import type { Compare, Edge, NativePolicy, Primitive } from '../../types'
import {
  closeIterator,
  closeIteratorAfterThrow,
  eachBuiltinEntry,
  eachBuiltinMember,
  entryPair,
  getIterator,
  iterationDone,
  nativeMapEntries,
  nativeSetValues,
  stepIterator,
} from '../../standard-prototypes'

const identity = (edge: Edge): unknown => (isNode(edge) ? edge : atomValue(edge))

/**
 * Steps an iterator as `for...of` steps it, calling `each` with each value until it returns true,
 * and closes it as `for...of` closes it when `each` stops early or throws.
 */
function walkIterator(iterator: object, each: (value: unknown) => boolean): boolean {
  const next = (iterator as { next?: unknown }).next
  for (;;) {
    const value = stepIterator(next, iterator)
    if (value === iterationDone) return false
    let stop: boolean
    try {
      stop = each(value)
    } catch (error) {
      closeIteratorAfterThrow(iterator)
      throw error
    }
    if (stop) {
      closeIterator(iterator)
      return true
    }
  }
}

/**
 * Calls `each` with every value that `for (const value of iterable)` would give, until it returns
 * true; returns whether it did.
 *
 * @remarks
 * When `@@iterator` is the built-in `Set.prototype.values`, the iterator it returns is fresh and
 * native, so it is stepped by the built-in `next` and, having no `return`, is not closed.
 */
export function eachMember(
  iterable: Iterable<unknown>,
  each: (value: unknown) => boolean,
): boolean {
  const method = (iterable as { [Symbol.iterator]?: unknown })[Symbol.iterator]
  return method === nativeSetValues
    ? eachBuiltinMember(iterable, each)
    : walkIterator(getIterator(iterable, method), each)
}

/**
 * Calls `each` with every entry that `for (const [key, value] of iterable)` would give, until it
 * returns true; returns whether it did. When `@@iterator` is the built-in `Map.prototype.entries`,
 * the iterator is fresh and native: it is stepped by the built-in `next`, its `[key, value]` arrays
 * are read by index, which nothing can observe, and it has no `return` to close.
 */
export function eachEntry(
  iterable: Iterable<unknown>,
  each: (key: unknown, value: unknown) => boolean,
): boolean {
  const method = (iterable as { [Symbol.iterator]?: unknown })[Symbol.iterator]
  return method === nativeMapEntries
    ? eachBuiltinEntry(iterable, each)
    : eachIteratedEntry(getIterator(iterable, method), each)
}

function eachIteratedEntry(
  iterator: object,
  each: (key: unknown, value: unknown) => boolean,
): boolean {
  return walkIterator(iterator, (entry) => {
    const pair = entryPair(entry)
    return each(pair[0], pair[1])
  })
}

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

/** How a collection's entries are read and written: with the built-in methods, or through the
 * object's own methods when it is a wrapper, such as a Vue reactive proxy. */
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
 * holds runs; a wrapper, such as a Vue reactive proxy, holds no entries of its own and uses `own`,
 * so its effects run.
 *
 * @param operations - Type-owned entry shape and the two ways to access entries.
 */
export function collectionSurface(operations: {
  builtin: CollectionAccess
  own: CollectionAccess
  readonly width: number
  read: (entry: unknown, slot: number, strict: boolean) => unknown
}): Pick<NativePolicy, 'aligned' | 'matches' | 'publish'> {
  const { width } = operations
  const walk = (
    node: readonly Edge[],
    current: object | undefined,
    visit: Compare,
    strict: boolean,
    access: CollectionAccess,
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
  const entriesOf = (current: object, access: CollectionAccess): unknown[] => {
    const present: unknown[] = []
    const entries = access.open(current)
    for (let step = access.step(entries); step.done !== true; step = access.step(entries))
      for (let slot = 0; slot < width; slot += 1)
        present.push(operations.read(step.value, slot, true))
    return present
  }
  const matches: NativePolicy['matches'] = (node, current, visit, _fresh, wrapped) => {
    const access = wrapped === true ? operations.own : operations.builtin
    return (
      access.size(current) === node.edges.length / width &&
      walk(node.edges, current, visit, true, access)
    )
  }
  return {
    matches,
    aligned: (node, current, visit, wrapped, prototype) => {
      walk(
        node.edges,
        current,
        (actual, edge) => {
          if (isNode(edge)) visit(actual, edge)
          return true
        },
        false,
        current !== undefined && wrapped?.(current, prototype) === true
          ? operations.own
          : operations.builtin,
      )
    },
    publish(node, current, resolve, _owner, note) {
      const edges = node.edges
      const access = note?.wrapped === true ? operations.own : operations.builtin
      const present = entriesOf(current, access)
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
