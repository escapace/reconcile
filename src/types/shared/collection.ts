import { atomValue, isNode } from '../../graph/edge'
import { isObject } from '../../object-property'
import type { Compare, Edge, NativePolicy, Primitive, Resolve } from '../../types'
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

/**
 * Builds the ordered collection walker of a Map or Set publication facet.
 *
 * @param operations - Type-owned entry shape and replacement rules.
 */
export function collectionSurface(operations: {
  readonly width: number
  iterator: (current: object) => Iterator<unknown>
  read: (entry: unknown, slot: number, strict: boolean) => unknown
  replace: (edges: readonly Edge[], current: object, resolve: Resolve) => void
  size: (current: object) => number
}): Pick<NativePolicy, 'aligned' | 'matches' | 'publish'> {
  const { width } = operations
  const walk = (
    node: readonly Edge[],
    current: object | undefined,
    visit: Compare,
    strict = false,
  ): boolean => {
    const previous = current === undefined ? undefined : operations.iterator(current)
    for (let index = 0; index < node.length; index += width) {
      const entry: unknown = previous?.next().value
      for (let slot = 0; slot < width; slot += 1) {
        if (!strict && !isNode(node[index + slot])) continue
        if (!visit(operations.read(entry, slot, strict), node[index + slot])) return false
      }
    }
    return true
  }
  const matches: NativePolicy['matches'] = (node, current, visit) =>
    operations.size(current) === node.edges.length / width && walk(node.edges, current, visit, true)
  return {
    matches,
    aligned: (node, current, visit) => {
      walk(node.edges, current, (actual, edge) => {
        if (isNode(edge)) visit(actual, edge)
        return true
      })
    },
    publish(node, current, resolve) {
      if (!matches(node, current, (actual, edge) => Object.is(resolve(edge), actual)))
        operations.replace(node.edges, current, resolve)
      return true
    },
  }
}
