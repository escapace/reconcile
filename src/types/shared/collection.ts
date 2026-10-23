import { atomValue, isNode } from '../../graph/edge'
import { isObject } from '../../object-property'
import type { Compare, Edge, NativePolicy, Primitive } from '../../types'
import {
  closeIterator,
  closeIteratorAfterThrow,
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
 * native, so it is stepped directly and, having no `return`, is not closed.
 */
export function eachMember(
  iterable: Iterable<unknown>,
  each: (value: unknown) => boolean,
): boolean {
  const method = (iterable as { [Symbol.iterator]?: unknown })[Symbol.iterator]
  if (method !== nativeSetValues) return walkIterator(getIterator(iterable, method), each)
  const iterator = Reflect.apply(
    nativeSetValues as () => unknown,
    iterable,
    [],
  ) as SetIterator<unknown>
  for (let step = iterator.next(); step.done !== true; step = iterator.next())
    if (each(step.value)) return true
  return false
}

/**
 * Calls `each` with every entry that `for (const [key, value] of iterable)` would give, until it
 * returns true; returns whether it did. When `@@iterator` is the built-in `Map.prototype.entries`,
 * the iterator is fresh and native: its `[key, value]` arrays are read by index, which nothing can
 * observe, and it has no `return` to close.
 */
export function eachEntry(
  iterable: Iterable<unknown>,
  each: (key: unknown, value: unknown) => boolean,
): boolean {
  const method = (iterable as { [Symbol.iterator]?: unknown })[Symbol.iterator]
  if (method === nativeMapEntries) return eachNativeEntry(iterable, each)
  return eachIteratedEntry(getIterator(iterable, method), each)
}

/**
 * Calls `each` with every entry that `for (const [key, value] of entries)` would give, where
 * `entries` is what calling `method` on a `Map` returned, as `map.entries()` or
 * `map[Symbol.iterator]()` returns it; returns whether `each` returned true. The built-in method's
 * result is a fresh native iterator, which returns itself as its iterator.
 */
export function eachOpenedEntry(
  entries: unknown,
  method: unknown,
  each: (key: unknown, value: unknown) => boolean,
): boolean {
  if (method === nativeMapEntries) return eachNativeStep(entries as MapIterator<unknown>, each)
  return eachIteratedEntry(getIterator(entries), each)
}

function eachNativeEntry(
  map: Iterable<unknown>,
  each: (key: unknown, value: unknown) => boolean,
): boolean {
  return eachNativeStep(
    Reflect.apply(nativeMapEntries as () => unknown, map, []) as MapIterator<unknown>,
    each,
  )
}

function eachNativeStep(
  iterator: MapIterator<unknown>,
  each: (key: unknown, value: unknown) => boolean,
): boolean {
  for (let step = iterator.next(); step.done !== true; step = iterator.next()) {
    const entry = step.value as readonly [unknown, unknown]
    if (each(entry[0], entry[1])) return true
  }
  return false
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

/** How a collection's entries are read and written: through the object's own methods, as
 * application code does, or with the built-in methods. */
export interface CollectionAccess {
  iterator: (current: object) => Iterator<unknown>
  /** Writes one entry: a `Map` key and value, or a `Set` member (`value` unused). */
  put: (current: object, key: unknown, value: unknown) => void
  remove: (current: object, key: unknown) => void
  size: (current: object) => number
}

/**
 * Builds the ordered collection walker of a Map or Set publication facet.
 *
 * @remarks
 * An object from `current` is read and written through `own`, as application code would. A new
 * copy that this call allocated uses `builtin`, so a subclass's override does not run on an object
 * its constructor never initialized; a wrapper exposing one, such as Vue's, uses `own`.
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
    const previous = current === undefined ? undefined : access.iterator(current)
    for (let index = 0; index < node.length; index += width) {
      const entry: unknown = previous?.next().value
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
    const entries = access.iterator(current)
    for (let step = entries.next(); step.done !== true; step = entries.next())
      for (let slot = 0; slot < width; slot += 1)
        present.push(operations.read(step.value, slot, true))
    return present
  }
  const matches: NativePolicy['matches'] = (node, current, visit, fresh) => {
    const access = fresh === true ? operations.builtin : operations.own
    return (
      access.size(current) === node.edges.length / width &&
      walk(node.edges, current, visit, true, access)
    )
  }
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
        operations.own,
      )
    },
    publish(node, current, resolve, _owner, note) {
      const edges = node.edges
      const access = note?.fresh === true ? operations.builtin : operations.own
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
      if (width === 2)
        for (let index = 0; index < position; index += 1) {
          const value = resolve(edges[index * 2 + 1])
          if (!Object.is(present[index * 2 + 1], value))
            access.put(current, present[index * 2], value)
        }
      for (let index = position; index < count; index += 1)
        access.remove(current, present[index * width])
      for (let index = position; index < wanted; index += 1)
        access.put(
          current,
          resolve(edges[index * width]),
          width === 2 ? resolve(edges[index * width + 1]) : undefined,
        )
      return true
    },
  }
}
