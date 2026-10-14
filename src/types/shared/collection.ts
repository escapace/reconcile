import { isNode } from '../../graph/edge'
import type { Compare, Edge, NativePolicy, Resolve } from '../../types'

const identity = (edge: Edge): unknown => (isNode(edge) ? edge : edge.value)
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
  for (const [key, index] of entries) {
    const first = edges[index]
    result.push(isNode(first) ? first : { value: key })
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
