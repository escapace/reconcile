import { atomValue, isNode } from './graph/edge'
import { finalizationConstructionImpossible } from './error'
import { immutableHead, immutableSelections } from './graph/immutable-selection'
import { closeRequirements } from './graph/requirements'
import { isObject } from './object-property'
import type {
  CapturedNode,
  Edge,
  FinalizedReference,
  ImmutableProblem,
  ImmutableRecord,
  ImmutableRegistry,
  NodeEdge,
  Primitive,
  ReuseNode,
} from './types'

const NO_FACTS: ReadonlySet<number> = /* @__PURE__ */ new Set()

/** The complete object-child list of each object a finalization walk visited to the end, which
 * compilation takes instead of reading again (Produce.SettledChildren). */
export type Walked = ReadonlyMap<object, readonly object[]> | undefined

/**
 * Compiles complete immutable ownership and child-binding facts before selection.
 *
 * @remarks
 * With `fold`, an object first met inside a fixed node's subtree gets no node of its own: its
 * edges to registered nodes become the edges of the fixed node whose walk met it.
 */
export function compileImmutable(
  types: ImmutableRegistry,
  result: FinalizedReference,
  kindOf: (value: object) => symbol,
  walked: Walked,
  fold: boolean,
): ImmutableProblem {
  const records: ImmutableRecord[] = []
  // A per-compile mark on the private finalized references replaces two identity tables; a
  // reference marked by another compile of the same graph carries a different mark.
  const mark = {}
  // The fixed nodes: the special targets, registered before the structural records.
  const fixed: NodeEdge[] = []
  const locallyReusable: boolean[] = []
  const parents: number[][] = []
  // The edge of each node by its object; a fixed subtree that reaches an object registered
  // elsewhere resolves to its node.
  const nodes = new Map<object, NodeEdge>()
  const register = (target: object, entry: ImmutableRecord): NodeEdge => {
    const index = records.length
    const reference = { node: index }
    nodes.set(target, reference)
    records.push(entry)
    locallyReusable[index] = true
    parents[index] = []
    return reference
  }
  const special = (target: object): NodeEdge => {
    const registered = nodes.get(target)
    if (registered !== undefined) return registered
    const reference = register(target, { edges: [], payload: undefined, target })
    fixed.push(reference)
    return reference
  }
  // Registers every special target the finalized result reaches, children in slot order.
  // Preserve the settled native observation boundary before structural reuse checks.
  const discover = (): void => {
    const references = [result]
    while (references.length !== 0) {
      const reference = references.pop()!
      if (reference.discoveredBy === mark) continue
      reference.discoveredBy = mark
      if (reference.layout === undefined) special(reference.target)
      else {
        const children = (reference as ReuseNode).children
        for (let index = children.length - 1; index >= 0; index -= 1)
          if (isObject(children[index])) references.push(children[index] as FinalizedReference)
      }
    }
  }
  discover()
  const edge = (value: unknown): Edge => {
    if (!isObject(value)) return value as Primitive
    const reference = value as FinalizedReference
    return reference.layout === undefined
      ? nodes.get(reference.target)!
      : collect(reference as ReuseNode)
  }
  const collect = (record: ReuseNode): NodeEdge => {
    if (record.collectedBy === mark) return record.collectedAs!
    record.collectedBy = mark
    const target = record.target
    // Every reference to one object has one node; discovery registered the special targets.
    const registered = nodes.get(target)
    if (registered !== undefined) return (record.collectedAs = registered)
    const edges: Edge[] = []
    const entry = { edges, payload: undefined as CapturedNode | undefined, target }
    const reference = register(target, entry)
    record.collectedAs = reference
    const index = reference.node
    const children = record.children
    let childrenReusable = true
    for (let slot = 0; slot < children.length; slot += 1) {
      const child = edge(children[slot])
      edges.push(child)
      if (isNode(child) && !locallyReusable[child.node]) childrenReusable = false
    }
    const payload: CapturedNode = {
      attributes: record.attributes,
      edges,
      keys: record.keys ?? [],
      layout: record.layout,
      observed: record.observed,
      pinned: undefined,
    }
    // A cycle back to this record reads only its target, so the entry gets its payload last.
    entry.payload = payload
    // Preserve child-first native checks and skip a parent already ruled out by
    // a discovered child failure. Cyclic implications close over finite facts below. A
    // settled record was read from its own unchanged, accessor-free base in this call, so
    // the readback would compare that base with itself.
    const reusable =
      childrenReusable &&
      (record.settled === true ||
        types.structural[record.layout.kind].reuse(payload, target, (actual, expected) =>
          Object.is(actual, isNode(expected) ? records[expected.node].target : atomValue(expected)),
        ))
    locallyReusable[index] = reusable
    // A failed parent is already a closure seed; only omit implications into it.
    // Passing parents can still fail later through a cycle, so retain their incidences.
    if (reusable) for (const child of edges) if (isNode(child)) parents[child.node].push(index)
    return reference
  }
  const root = (edge(result) as NodeEdge).node
  // Fixed nodes expose their children after structural collection: settled specials their
  // construction dependencies, unchanged leaves their whole subtree, so identity implications
  // cover every object the result keeps. A child registered elsewhere resolves to its node.
  // Without seeds nothing is unavailable (Requirements.close_no_seeds).
  if (fixed.length !== 0)
    registerFixed({ fold, kindOf, parents, records, types, walked }, fixed, nodes, special)
  const seeds: number[] = []
  for (let index = 0; index < records.length; index += 1)
    if (!locallyReusable[index]) seeds.push(index)
  const unavailable = seeds.length === 0 ? NO_FACTS : closeRequirements(seeds, parents)
  return { records, root, unavailable }
}

/** The compilation state fixed-node registration reads and fills. */
interface FixedState {
  readonly fold: boolean
  readonly parents: number[][]
  readonly records: ImmutableRecord[]
  readonly types: ImmutableRegistry
  readonly walked: Walked
  readonly kindOf: (value: object) => symbol
}

/**
 * Registers each fixed node's object children, in registration order. A child already
 * registered, or any child without `fold`, becomes an edge; with `fold`, an object first met
 * inside a fixed subtree gets no node: its children become the fixed node's.
 */
function registerFixed(
  state: FixedState,
  fixed: readonly NodeEdge[],
  nodes: ReadonlyMap<object, NodeEdge>,
  special: (value: object) => NodeEdge,
): void {
  const { fold, kindOf, parents, records, types, walked } = state
  // The fixed node whose children `child` registers, and its edges.
  let owner = 0
  let edges: Edge[] = []
  // The folded objects, and those whose children are still to be visited.
  let folded: Set<object> | undefined
  const unvisited: object[] = []
  const child = (value: unknown): boolean => {
    if (!isObject(value)) return false
    const known = nodes.get(value)
    if (known !== undefined || !fold) {
      const reference = known ?? special(value)
      edges.push(reference)
      parents[reference.node].push(owner)
    } else if (!(folded ??= new Set()).has(value)) {
      folded.add(value)
      unvisited.push(value)
    }
    return false
  }
  // Without `fold`, a child registers a fixed node, which this loop then visits too.
  for (let index = 0; index < fixed.length; index += 1) {
    owner = fixed[index].node
    const target = records[owner].target
    edges = []
    eachChild(types, kindOf, target, walked?.get(target), child)
    for (let next = unvisited.pop(); next !== undefined; next = unvisited.pop())
      eachChild(types, kindOf, next, walked?.get(next), child)
    records[owner] = { edges, payload: undefined, target }
  }
}

/**
 * Visits a fixed target's object children: those a finalization walk that visited all of them
 * listed (Produce.SettledChildren), otherwise read from the target.
 */
function eachChild(
  types: ImmutableRegistry,
  kindOf: (value: object) => symbol,
  target: object,
  children: readonly object[] | undefined,
  visit: (value: unknown) => boolean,
): void {
  if (children === undefined) types.policies[kindOf(target)].someChild(target, Reflect.get, visit)
  else for (let index = 0; index < children.length; index += 1) visit(children[index])
}

/**
 * Keeps the retained targets, allocates the fresh ones and writes their captured slots once every
 * target exists; undefined when a copy cannot hold its slots.
 *
 * @remarks
 * Every fresh node is an object, array, `Map` or `Set`, whose copy needs no other copy to exist
 * first, so the fresh nodes are allocated in ascending order, the order
 * `Construction.schedule_shells_only` gives for shells only.
 */
function publishFresh(
  types: ImmutableRegistry,
  records: readonly ImmutableRecord[],
  retained: readonly boolean[],
): object[] | undefined {
  const targets: object[] = []
  const resolve = (value: Edge): unknown => (isNode(value) ? targets[value.node] : atomValue(value))
  for (let index = 0; index < records.length; index += 1) {
    const record = records[index]
    targets[index] = retained[index]
      ? record.target
      : types.structural[record.payload!.layout.kind].allocate(record.payload!)
  }
  for (let index = 0; index < records.length; index += 1) {
    if (retained[index]) continue
    const record = records[index]
    const node = record.payload!
    const target = targets[index]
    if (!types.structural[node.layout.kind].fill(node, target, resolve)) return undefined
    // A copy of a frozen, sealed or otherwise non-extensible object is non-extensible too; with
    // the attributes its properties keep, a copy of a frozen object is frozen.
    if (!Object.isExtensible(record.target)) Object.preventExtensions(target)
  }
  return targets
}

/**
 * Retains compatible base identities and publishes fresh nodes for rejected reuse candidates.
 *
 * @remarks
 * Child-first native checks supply immutable reuse facts. The finite closure and compact selector
 * resolve child-identity implications and distinct storage ownership. Only selected fresh nodes
 * are written, after every target is allocated. Working structural stores never escape.
 * Settled specials participate as fixed graph nodes, including explicit backing-buffer edges.
 * Their scalar payload preservation remains a native premise; selection never writes them.
 *
 * @param result - Private finalized root whose structural nodes have not yet been analyzed.
 * @returns The selected application root after fresh containers receive their captured edges.
 * @internal
 */
export function restoreIdentities(
  types: ImmutableRegistry,
  result: FinalizedReference,
  strict: boolean,
  kindOf: (value: object) => symbol,
  walked: Walked,
): object | undefined {
  // A result kept whole is the only registered node: every other object folds into it and nothing
  // can be unavailable, so the head keeps it.
  if (!strict && result.layout === undefined) return result.target
  // The first, non-strict attempt folds the objects inside fixed subtrees.
  const problem = compileImmutable(types, result, kindOf, walked, !strict)
  const { root } = problem
  // With nothing unavailable the head keeps every record, which allocates nothing and writes
  // nothing, so the root keeps its own target.
  if (problem.unavailable.size === 0) return result.target
  // Fixed specials contribute the same score to every plan; only structural retention varies.
  // The stream's first mask is often determined without searching; the search starts only if
  // that mask cannot be built, and its first mask, already tried, is skipped.
  const head = immutableHead(problem)
  const targets = publishFirst(types, problem, head)
  if (targets !== undefined) return targets[root]
  if (!strict) return undefined
  throw finalizationConstructionImpossible()
}

// Publishes the head, then each later mask the stream ranks, until one can be built.
function publishFirst(
  types: ImmutableRegistry,
  problem: ImmutableProblem,
  head: boolean[] | undefined,
): object[] | undefined {
  const records = problem.records
  if (head !== undefined) {
    const targets = publishFresh(types, records, head)
    if (targets !== undefined) return targets
  }
  let skip = head !== undefined
  for (const selection of immutableSelections(problem)) {
    if (skip) {
      skip = false
      continue
    }
    const targets = publishFresh(types, records, selection)
    if (targets !== undefined) return targets
  }
  return undefined
}
