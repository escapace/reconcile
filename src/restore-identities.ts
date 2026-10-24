import { atomValue, isNode } from './graph/edge'
import { recognize } from './adapters/recognition'
import { smallAdd, smallHas, smallSet, type SmallSet } from './graph/small-set'
import { finalizationConstructionImpossible } from './error'
import { constructionOrder } from './graph/construction'
import { constructionDependencies } from './graph/construction-facts'
import { immutableHead, immutableSelections } from './graph/immutable-selection'
import { closeRequirements } from './graph/requirements'
import { isObject } from './object-property'
import { MAP_KIND } from './types/map'
import { SET_KIND } from './types/set'
import { builtinMapSize, builtinSetSize } from './standard-prototypes'
import type {
  CapturedNode,
  Edge,
  FinalizedReference,
  ImmutableProblem,
  ImmutableRecord,
  ImmutableRegistry,
  NativeOwners,
  Primitive,
  ReuseNode,
} from './types'

const NO_FACTS: ReadonlySet<number> = /* @__PURE__ */ new Set()

/**
 * An edge to a registered node. `view` is the object the slot held when it is another view of the
 * node's target: a kept node keeps that view at that slot.
 */
interface ViewEdge {
  readonly node: number
  readonly view: object | undefined
}

/** Facts finalization read in this call, which compilation takes instead of reading again. */
export interface FinalizationFacts {
  /** The complete object-child list of an object a walk visited to the end
   * (Produce.SettledChildren). */
  readonly walked: ReadonlyMap<object, readonly object[]> | undefined
}

/**
 * Compiles complete immutable ownership and child-binding facts before selection.
 *
 * @remarks
 * With `fold`, an object first met inside a fixed node's subtree gets no node of its own: its
 * storage still joins the fixed storages, and its edges to registered nodes become the edges of
 * the fixed node whose walk met it. Produce.FoldedLeaves proves the selector then has the same
 * choices whenever no storage conflicts, which a caller that folds must treat as a rejection.
 */
export function compileImmutable(
  types: ImmutableRegistry,
  result: FinalizedReference,
  kindOf: (value: object) => symbol = (value) => recognize(types, value),
  facts?: FinalizationFacts,
  fold = false,
): ImmutableProblem {
  const records: ImmutableRecord[] = []
  // A per-compile mark on the private finalized references replaces two identity tables; a
  // reference marked by another compile of the same graph carries a different mark.
  const mark = {}
  // Special targets by identity, created on the first one, and the fixed nodes they register.
  let specials: Map<object, ViewEdge> | undefined
  const fixed: ViewEdge[] = []
  const locallyReusable: boolean[] = []
  const parents: number[][] = []
  const storages: object[] = []
  // The edge of each node by its object; a fixed subtree that reaches an object registered
  // elsewhere resolves to its node.
  const nodes = new Map<object, ViewEdge>()
  // The edge to `node` from a slot that holds `target`.
  const viewed = (node: ViewEdge, target: object): ViewEdge =>
    records[node.node].target === target ? node : { node: node.node, view: target }
  const register = (storage: object, entry: ImmutableRecord): ViewEdge => {
    const index = records.length
    const reference = { node: index, view: undefined }
    nodes.set(storage, reference)
    storages[index] = storage
    records.push(entry)
    locallyReusable[index] = true
    parents[index] = []
    return reference
  }
  const special = (target: object): ViewEdge => {
    const previous = specials?.get(target)
    if (previous !== undefined) return previous
    const registered = nodes.get(target)
    const reference =
      registered === undefined
        ? register(target, { edges: [], payload: undefined, settled: undefined, target })
        : viewed(registered, target)
    ;(specials ??= new Map()).set(target, reference)
    if (registered === undefined) fixed.push(reference)
    return reference
  }
  // Registers every special target the finalized result reaches, children in slot order.
  // Preserve the settled native observation boundary before structural reuse checks. A view
  // stands for the reference it views.
  const discover = (): void => {
    const references = [result]
    while (references.length !== 0) {
      const reference = references.pop()!
      if (reference.discoveredBy === mark) continue
      reference.discoveredBy = mark
      if (reference.viewOf !== undefined) references.push(reference.viewOf)
      else if (reference.layout === undefined) special(reference.target)
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
    if (reference.viewOf !== undefined) {
      const node = edge(reference.viewOf) as ViewEdge
      return viewed(nodes.get(storages[node.node])!, reference.target)
    }
    return reference.layout === undefined
      ? specials!.get(reference.target)!
      : collect(reference as ReuseNode)
  }
  const collect = (record: ReuseNode): ViewEdge => {
    if (record.collectedBy === mark) return record.collectedAs as ViewEdge
    record.collectedBy = mark
    const target = record.target
    const registered = nodes.get(target)
    if (registered !== undefined) return (record.collectedAs = viewed(registered, target))
    const edges: Edge[] = []
    const entry = {
      edges,
      payload: undefined as CapturedNode | undefined,
      settled: undefined as boolean | undefined,
      target,
    }
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
    // Only target is read through a pending cycle. Complete the same private entry
    // at the original replacement boundary, preserving both native property reads.
    entry.payload = payload
    entry.settled = record.settled
    entry.target = record.target
    // Preserve child-first native checks and skip a parent already ruled out by
    // a discovered child failure. Cyclic implications close over finite facts below. A
    // settled record was read from its own unchanged, accessor-free base in this call, so
    // the readback would compare that base with itself.
    const reusable =
      childrenReusable &&
      (record.settled === true ||
        types.structural[record.layout.kind].reuse(payload, record.target, (actual, expected) => {
          const wanted = isNode(expected)
            ? ((expected as ViewEdge).view ?? records[expected.node].target)
            : atomValue(expected)
          // Another view of the object the slot holds is that object (StorageViews).
          return Object.is(actual, wanted)
        }))
    locallyReusable[index] = reusable
    // A failed parent is already a closure seed; only omit implications into it.
    // Passing parents can still fail later through a cycle, so retain their incidences.
    if (reusable) for (const child of edges) if (isNode(child)) parents[child.node].push(index)
    return reference
  }
  const root = (edge(result) as ViewEdge).node
  // Fixed nodes expose their children after structural collection: settled specials their
  // construction dependencies, unchanged leaves their whole subtree, so storage ownership
  // and identity implications cover every object the result keeps. A child registered
  // elsewhere resolves to its node.
  // Without fixed nodes no storage is fixed, and without seeds nothing is unavailable
  // (Requirements.close_no_seeds).
  const fixedStorage = fixed.length === 0 ? undefined : smallSet<object>()
  let conflict =
    fixedStorage !== undefined &&
    registerFixed(
      { facts, fold, kindOf, parents, records, storages, types },
      fixed,
      nodes,
      special,
      fixedStorage,
    )
  const seeds: number[] = []
  for (let index = 0; index < records.length; index += 1)
    if (!locallyReusable[index]) seeds.push(index)
  const unavailable = seeds.length === 0 ? NO_FACTS : closeRequirements(seeds, parents)
  if (fixedStorage !== undefined && claimsFixed(records, storages, unavailable, fixedStorage))
    conflict = true
  return { conflict, records, root, storages, unavailable }
}

/** Whether a record the result could keep has a fixed storage. */
function claimsFixed(
  records: readonly ImmutableRecord[],
  storages: readonly object[],
  unavailable: ReadonlySet<number>,
  fixedStorage: SmallSet<object>,
): boolean {
  for (let index = 0; index < records.length; index += 1)
    if (
      records[index].payload !== undefined &&
      !unavailable.has(index) &&
      smallHas(fixedStorage, storages[index])
    )
      return true
  return false
}

/** The compilation state fixed-node registration reads and fills. */
interface FixedState {
  readonly facts: FinalizationFacts | undefined
  readonly fold: boolean
  readonly parents: number[][]
  readonly records: ImmutableRecord[]
  readonly storages: object[]
  readonly types: ImmutableRegistry
  readonly kindOf: (value: object) => symbol
}

/**
 * Registers each fixed node's storage and object children, in registration order, and reports
 * whether a storage was claimed twice. A child already registered, or any child without `fold`,
 * becomes an edge; with `fold`, an object first met inside a fixed subtree gets no node: its
 * storage joins the fixed storages and its children become the fixed node's
 * (Produce.FoldedLeaves).
 */
function registerFixed(
  state: FixedState,
  fixed: readonly ViewEdge[],
  nodes: ReadonlyMap<object, ViewEdge>,
  special: (value: object) => ViewEdge,
  fixedStorage: SmallSet<object>,
): boolean {
  const { facts, fold, kindOf, parents, records, storages, types } = state
  let conflict = false
  const claim = (storage: object): void => {
    if (smallHas(fixedStorage, storage)) conflict = true
    smallAdd(fixedStorage, storage)
  }
  // The fixed node whose children `child` registers, and its edges.
  let owner = 0
  let edges: Edge[] = []
  // The storages of folded objects, and the objects whose children are still to be visited.
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
      claim(value)
      unvisited.push(value)
    }
    return false
  }
  // Without `fold`, a child registers a fixed node, which this loop then visits too.
  for (let index = 0; index < fixed.length; index += 1) {
    owner = fixed[index].node
    const target = records[owner].target
    claim(storages[owner])
    edges = []
    eachChild(types, kindOf, target, facts?.walked?.get(target), child)
    for (let next = unvisited.pop(); next !== undefined; next = unvisited.pop())
      eachChild(types, kindOf, next, facts?.walked?.get(next), child)
    records[owner] = { edges, payload: undefined, settled: undefined, target }
  }
  return conflict
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
 * Keeps the retained targets, allocates the fresh ones in construction order and writes their
 * captured edges once every target exists.
 */
function publishFresh(
  types: ImmutableRegistry,
  records: readonly ImmutableRecord[],
  retained: readonly boolean[],
  order: readonly number[],
): object[] | undefined {
  const targets: object[] = []
  // Native ownership found while allocating; a literal holds the field as its own data.
  const owners: NativeOwners = { nativeOwners: undefined }
  // A kept child is the view its slot held (ViewEdge).
  const resolve = (value: Edge): unknown => {
    if (!isNode(value)) return atomValue(value)
    const view = (value as ViewEdge).view
    return view !== undefined && retained[value.node] ? view : targets[value.node]
  }
  for (let index = 0; index < records.length; index += 1)
    if (retained[index]) targets[index] = records[index].target
  for (let position = 0; position < order.length; position += 1) {
    const index = order[position]
    const node = records[index].payload!
    const target = types.policies[node.layout.kind].allocate(node, resolve, owners)
    if (target === undefined) return undefined
    targets[index] = target
  }
  for (let index = 0; index < records.length; index += 1)
    if (!retained[index] && !fill(types, records[index], targets[index], resolve)) return undefined
  return targets
}

// Writes the captured edges of a fresh record's target; false when the target cannot hold them.
function fill(
  types: ImmutableRegistry,
  record: ImmutableRecord,
  target: object,
  resolve: (value: Edge) => unknown,
): boolean {
  const node = record.payload!
  const policy = types.policies[node.layout.kind]
  for (let slot = 0; slot < node.edges.length; slot += 1)
    policy.freshWrite(node, target, slot, resolve)
  // A `Map` or `Set` that holds one node as two keys or members, as when two keys share one
  // special copy, cannot be copied: no plan that copies it can be built.
  if (collapses(node, target)) return false
  // A copy of a frozen, sealed or otherwise non-extensible object is non-extensible too; with
  // the attributes its properties keep, a copy of a frozen object is frozen.
  if (!Object.isExtensible(record.target)) Object.preventExtensions(target)
  return true
}

// Whether a new `Map` or `Set` holds fewer keys or members than its node has.
const collapses = (node: CapturedNode, target: object): boolean =>
  node.layout.kind === MAP_KIND
    ? builtinMapSize(target) * 2 !== node.edges.length
    : node.layout.kind === SET_KIND && builtinSetSize(target) !== node.edges.length

// Publishes one plan in construction order; undefined when it cannot be constructed or built.
function publishPlan(
  types: ImmutableRegistry,
  records: readonly ImmutableRecord[],
  dependencies: ReadonlyArray<readonly number[]>,
  retained: readonly boolean[],
): object[] | undefined {
  const order = constructionOrder(dependencies, retained)
  return order === undefined ? undefined : publishFresh(types, records, retained, order)
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
  kindOf?: (value: object) => symbol,
  facts?: FinalizationFacts,
): object | undefined {
  // A result kept whole is the only registered node: every other object folds into it and nothing
  // can be unavailable. Folding tells objects apart by storage, so no two folded storages clash,
  // and the head keeps it.
  if (!strict && result.layout === undefined && result.viewOf?.layout === undefined)
    return result.target
  // The first, non-strict attempt folds the objects inside fixed subtrees; a conflict rejects it.
  const problem = compileImmutable(types, result, kindOf, facts, !strict)
  const { records, root } = problem
  // A kept root is the view the result holds, which can be another view of its node's storage.
  const shown = (target: object): object =>
    target === records[root].target ? result.target : target
  // Fixed leaves claim their storage unconditionally. When one shares storage with another
  // node, the kernel could no longer weigh the larger compatible subset, so finalization
  // redoes the sealed full pass instead.
  if (!strict && problem.conflict) return undefined
  // Fixed specials contribute the same score to every plan. Only structural
  // retention varies; their private fresh choices cannot claim settled storage.
  // The stream's first mask is often determined without searching; the search starts only if
  // that mask cannot be built, and its first mask, already tried, is skipped.
  const head = immutableHead(problem)
  // A head keeping every record allocates nothing: its construction order is empty
  // (Construction.schedule_all_retained) and publication writes nothing, so the root keeps its
  // own target.
  if (head !== undefined && problem.unavailable.size === 0) return result.target
  const targets = publishFirst(types, problem, head)
  if (targets !== undefined) return shown(targets[root])
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
  const dependencies = records.map((record) => constructionDependencies(types, record.payload))
  if (head !== undefined) {
    const targets = publishPlan(types, records, dependencies, head)
    if (targets !== undefined) return targets
  }
  let skip = head !== undefined
  for (const selection of immutableSelections(problem)) {
    if (skip) {
      skip = false
      continue
    }
    const targets = publishPlan(types, records, dependencies, selection)
    if (targets !== undefined) return targets
  }
  return undefined
}
