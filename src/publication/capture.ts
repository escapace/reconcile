import { isNode } from '../graph/edge'
import { hasOwn, isObject } from '../object-property'
import { recognize } from '../adapters/recognition'
import { storageIdentity } from '../adapters/vue'
import { noValue } from '../types/shared/empty'
import type {
  BuildingNode,
  CapturedGraph,
  CapturedNode,
  CaptureSink,
  Edge,
  CapturePolicy,
  NativeRegistry,
  NodeEdge,
  PublicationPolicy,
  PublicationRegistry,
} from '../types'

/**
 * Traverses native observations through a graph or incremental snapshot sink.
 *
 * @remarks
 * Memoize the private reference before observing children. Construction edges may precede begin;
 * their child must finish before the parent's constructor consumes its response. Synchronous
 * delivery preserves iterator cleanup and accessor effects at the native module boundary. A sink
 * with `adopt` may decide a child itself; the snapshot sink has none.
 */
export function traverse<
  R extends { readonly node: number },
  P extends CapturePolicy = CapturePolicy,
>(
  types: NativeRegistry<P>,
  value: unknown,
  sink: CaptureSink<R, P>,
  knownKind?: symbol,
  mode: 'publication' | 'snapshot' = 'publication',
): Edge<R> {
  const references = new Map<object, Edge<R>>()
  let size = 0
  const visit = (source: unknown, kind?: symbol): Edge<R> => {
    if (!isObject(source)) return { value: source }
    const external = sink.existing?.(source)
    if (external !== undefined) return { value: external }
    return references.get(source) ?? observe(source, kind)
  }
  const observe = (source: object, kind?: symbol): R => {
    const index = size++
    const reference = sink.reserve(index)
    references.set(source, reference)
    const policy: P = types.policies[kind ?? recognize(types, source)]
    policy.observe(
      source,
      (layout) => {
        sink.begin(source, reference, layout)
      },
      (value, key, knownKind, construction) => {
        const child =
          sink.adopt?.(reference, value, key, construction, references, observe, knownKind) ??
          visit(value, knownKind)
        sink.edge(reference, child, key)
        if (construction === true) {
          if (isNode(child)) {
            const layout = sink.layout(child)
            if (layout !== undefined) return types.policies[layout.kind].construction(layout)
          } else {
            const target = child.value
            return (isObject(target) ? sink.constructed?.(target) : undefined) ?? target
          }
        }
        return undefined
      },
      mode,
    )
    sink.finish(reference, policy)
    return reference
  }
  return visit(value, knownKind)
}

/**
 * Captures `value`, aligned with `current` when supplied.
 *
 * @remarks
 * Aligned capture reads, for each own-property edge of a node whose aligned current object
 * has the same kind, the occupant of that slot right after the next value. A child that is
 * the occupant itself is walked once and kept as an atom edge holding the object when its
 * kind needs no construction input and has independent bindings and the walk meets neither
 * root. Everything the walk met is protected: no other position may retain it, and a later
 * child found inside it is kept the same way or, once captured, pinned to itself. Candidate
 * discovery reuses the recorded occupants, so captured regions perform the same reads as an
 * unaligned capture.
 */
export function capture(
  types: PublicationRegistry,
  value: unknown,
  current?: object,
): CapturedGraph {
  const nodes: Array<BuildingNode | CapturedNode> = []
  const currents: Array<object | undefined> = []
  const occupants: Array<unknown[] | undefined> = []
  const sources: object[] = []
  const closure = new Set<object>()
  const protectedStorage = new Set<unknown>()
  // Occupant handed from the parent's aligned read to the child's reservation.
  let pending: object | undefined = current
  // A keepable kind needs no construction input and has independent bindings. Its subtree is
  // read once before it is kept; one that contains either root is captured instead, as full
  // capture requires, and everything the walk met is protected from reuse elsewhere. The walk
  // is an explicit stack over the publication observation surface: no records, no selection.
  // It stops at the first root it meets and forgets what it marked on the way.
  const keep = (candidate: object): boolean => {
    let policy = types.policies[recognize(types, candidate)]
    if (policy.bindings.tag !== 'independent' || policy.construction !== noValue) return false
    if (closure.has(candidate)) return true
    const visited: object[] = []
    const stack: object[] = []
    let source: object | undefined = candidate
    const edge = (child: unknown, _key?: PropertyKey, _kind?: symbol, construction?: boolean) => {
      if (isObject(child)) stack.push(child)
      // A view's constructor receives its actual buffer; the sample it builds is dropped.
      return construction === true ? child : undefined
    }
    while (source !== undefined) {
      if (!closure.has(source)) {
        if (source === value || source === current) {
          visited.forEach((marked) => closure.delete(marked))
          return false
        }
        closure.add(source)
        visited.push(source)
        policy.observe(source, noValue, edge)
      }
      source = stack.pop()
      if (source !== undefined) policy = types.policies[recognize(types, source)]
    }
    for (const marked of visited) protectedStorage.add(storageIdentity(marked))
    return true
  }
  // Own-property edges may keep the current occupant as an atom; construction edges never do.
  // The reference lookup happens once here, not again inside the visit.
  const adopt: CaptureSink<NodeEdge, PublicationPolicy>['adopt'] = (
    { node: parent },
    child,
    key,
    construction,
    references,
    observe,
    kind,
  ) => {
    const aligned = currents[parent]
    if (aligned === undefined || key === undefined || construction === true || !isObject(child))
      return undefined
    const known = references.get(child)
    const occupant: unknown = hasOwn(aligned, key) ? Reflect.get(aligned, key) : undefined
    if (
      known === undefined &&
      (Object.is(occupant, child) || (closure.size !== 0 && closure.has(child))) &&
      keep(child)
    ) {
      const edge = { value: child }
      references.set(child, edge)
      return edge
    }
    // One entry per own-property node edge, in edge order; atoms are not recorded.
    if (known === undefined || isNode(known)) (occupants[parent] ??= []).push(occupant)
    if (known !== undefined) return known
    pending = isObject(occupant) ? occupant : undefined
    return observe(child, kind)
  }
  const root = traverse(types, value, {
    adopt,
    begin(source, { node: index }, layout) {
      // The driver calls begin/edge only while this node is under construction.
      ;(nodes[index] as BuildingNode).layout = layout
      sources[index] = source
      const aligned = currents[index]
      if (aligned !== undefined && recognize(types, aligned) !== layout.kind)
        currents[index] = undefined
    },
    edge({ node: index }, child, key) {
      const node = nodes[index] as BuildingNode
      node.edges.push(child)
      if (key !== undefined) node.keys.push(key)
    },
    finish({ node: index }, policy) {
      // Native policies supply begin before returning; all graph nodes are sealed.
      nodes[index] = policy.seal(nodes[index] as CapturedNode)
    },
    layout: ({ node: index }) => nodes[index]?.layout,
    reserve(index) {
      nodes[index] = { edges: [], keys: [], layout: undefined }
      currents[index] = pending
      pending = undefined
      return { node: index }
    },
  })
  return { currents, nodes: nodes as CapturedNode[], occupants, protectedStorage, root, sources }
}
