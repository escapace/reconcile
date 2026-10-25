import { atomValue, isNode } from '../graph/edge'
import { matchesKind } from '../adapters/recognition'
import type {
  Candidate,
  Candidates,
  CapturedGraph,
  CapturedNode,
  Compare,
  Edge,
  NativeOwners,
  PublicationNote,
  PublicationRegistry,
} from '../types'
import { alignedReads, candidates } from './candidates'
import { constructionOrder } from '../graph/construction'
import { constructionDependencies } from '../graph/construction-facts'
import { denseArray } from '../standard-prototypes'

/**
 * What a pass leaves for the passes after it: the objects it found blocked, the node each object
 * it wrote was kept at, by object and by node, and its targets, which say what its readback saw.
 * Created by the first pass that is followed by another.
 */
interface Passes {
  readonly forbidden: Set<object>
  previousTargets: readonly object[]
  readonly written: Map<object, number>
  readonly writtenAt: Array<object | undefined>
}

/**
 * The decision of one pass: the object kept per node, the object an earlier decision requires at
 * a node not yet reached, and the objects reserved for a node, which only an object that is a
 * candidate at several nodes (`shared`) or one an earlier pass wrote can be.
 */
interface Decision {
  readonly domains: Candidates
  readonly kept: Array<object | undefined>
  readonly passes: Passes | undefined
  readonly records: readonly CapturedNode[]
  required: Array<object | undefined> | undefined
  readonly shared: ReadonlyMap<object, unknown> | undefined
  used: Set<object> | undefined
}

// The candidate of a node that is `identity`, if any.
function candidateOf(domain: readonly Candidate[], identity: object): Candidate | undefined {
  for (let index = 0; index < domain.length; index += 1)
    if (domain[index].identity === identity) return domain[index]
  return undefined
}

// Whether `x` is reserved for a node other than `c`: kept by an earlier decision of this pass, or
// written at another node by an earlier pass.
const reservedElsewhere = (state: Decision, c: number, x: object): boolean =>
  state.used?.has(x) === true && state.passes?.written.get(x) !== c

// Whether `x` may be kept at `c` as far as the passes and the decisions so far say: no pass found
// it blocked and no other node reserved it.
const admissible = (state: Decision, c: number, x: object): boolean =>
  state.passes?.forbidden.has(x) !== true && !reservedElsewhere(state, c, x)

// Reserves `x` when another node could claim it.
function reserve(state: Decision, x: object): void {
  if (state.shared?.has(x) === true || state.passes !== undefined) (state.used ??= new Set()).add(x)
}

// What the chain says about `c` keeping `x`: a pair already in the chain holds, and a node or
// object the chain pairs otherwise conflicts; undefined when the chain names neither.
function chained(chain: readonly unknown[], c: number, x: object): boolean | undefined {
  for (let index = 0; index < chain.length; index += 2) {
    if (chain[index] === c) return chain[index + 1] === x
    if (chain[index + 1] === x) return false
  }
  return undefined
}

// Whether node `c`, not the node being decided, keeps `x` when something is fixed at it: a node
// before `node` keeps what it was decided to, a pinned node the object it is, and a node an
// earlier decision requires an object at that object; undefined when nothing is fixed at `c`.
function fixedKeeps(state: Decision, node: number, c: number, x: object): boolean | undefined {
  if (c < node) return state.kept[c] === x
  const fixed = state.records[c].pinned ?? state.required?.[c]
  return fixed === undefined ? undefined : fixed === x
}

/**
 * Establishes that node `c` keeps `x` while `node` is being decided, extending `chain`, which
 * alternates nodes and objects, with the pairs that requires; false when it cannot. A pair
 * already in the chain holds, and a node or object the chain pairs otherwise conflicts. A node
 * something is fixed at must keep `x`. Otherwise `x` must be a candidate of `c` that no pass
 * found blocked and no other node reserved, and each fixed slot of `x` establishes that the node
 * at that slot keeps the object the slot holds (Spec.Reconcile.establish).
 */
function establish(state: Decision, node: number, chain: unknown[], c: number, x: object): boolean {
  const known = chained(chain, c, x)
  if (known !== undefined) return known
  const fixed = c === node ? undefined : fixedKeeps(state, node, c, x)
  if (fixed !== undefined) return fixed
  if (!admissible(state, c, x)) return false
  const candidate = candidateOf(state.domains[c], x)
  if (candidate === undefined) return false
  chain.push(c, x)
  const required = candidate.required
  for (let index = 0; index < required.length; index += 1)
    if (!establish(state, node, chain, required[index].node, required[index].identity)) return false
  return true
}

// Keeps `x` at `node` when its chain can be established: the objects the chain names are
// reserved and the nodes it names are required to keep them. Whether it was kept.
function keep(state: Decision, node: number, candidate: Candidate, x: object): boolean {
  if (candidate.required.length === 0) {
    if (!admissible(state, node, x)) return false
    state.kept[node] = x
    reserve(state, x)
    return true
  }
  const chain: unknown[] = []
  if (!establish(state, node, chain, node, x)) return false
  for (let index = 0; index < chain.length; index += 2) {
    const c = chain[index] as number
    const y = chain[index + 1] as object
    if (c === node) state.kept[node] = y
    else (state.required ??= denseArray<object | undefined>(state.records.length))[c] = y
    reserve(state, y)
  }
  return true
}

/**
 * Decides which current object each node keeps, in node order, which is the order of first visit:
 * a pinned node keeps the object it is; a node an earlier decision requires keeps that object; any
 * other node keeps the object an earlier pass wrote there when it still can, else the first of its
 * candidates that can be established. An object an earlier pass found blocked is never kept, and
 * one it wrote stays at its node or is dropped, so no object holds another node's writes. Nothing
 * is read or written: discovery read the candidates and the preflight checked them
 * (Spec.Reconcile.decide).
 */
function decide(
  records: readonly CapturedNode[],
  domains: Candidates,
  shared: ReadonlyMap<object, unknown> | undefined,
  passes: Passes | undefined,
): Array<object | undefined> {
  const size = records.length
  const state: Decision = {
    domains,
    kept: denseArray<object | undefined>(size),
    passes,
    records,
    required: undefined,
    shared,
    used: passes === undefined ? undefined : new Set(passes.written.keys()),
  }
  for (let node = 0; node < size; node += 1) decideNode(state, node)
  return state.kept
}

// Decides one node, as `decide` says.
function decideNode(state: Decision, node: number): void {
  const fixed = state.records[node].pinned ?? state.required?.[node]
  if (fixed !== undefined) {
    state.kept[node] = fixed
    return
  }
  const domain = state.domains[node]
  const before = state.passes?.writtenAt[node]
  const first = before === undefined ? undefined : candidateOf(domain, before)
  if (first !== undefined && keep(state, node, first, before!)) return
  for (let at = 0; at < domain.length; at += 1) {
    const candidate = domain[at]
    if (candidate !== first && keep(state, node, candidate, candidate.identity)) return
  }
}

/** The pass under way: the target of each node, which the callbacks read, the native owners found
 * among them, and whether every publication so far wrote nothing a readback would reject. */
interface Run {
  nativeOwners: Map<symbol, WeakMap<object, object>> | undefined
  targets: readonly object[]
  unchanged: boolean
}

/**
 * Publishes a captured graph into `root`: decides which current object each node keeps, allocates
 * the fresh ones, writes every node and reads the written objects back, in passes. A kept object
 * whose write does not take effect is blocked: the next pass decides again without it, and the
 * passes end when none is blocked. Pinned nodes are kept as they are: no preflight, publication or
 * readback inside. Returns false when the root cannot be kept: before any write when the decision
 * finds so, else after the pass that found it blocked (Spec.Reconcile.run).
 */
export function publishGraph(
  types: PublicationRegistry,
  graph: CapturedGraph,
  root: object,
): boolean {
  const records = graph.nodes
  // The channel between this call's preflights and publications.
  const note: PublicationNote = {
    facts: undefined,
    prototype: undefined,
    reads: undefined,
    unchanged: false,
  }
  const domains = candidates(types, records, root, graph, note)
  const run: Run = {
    nativeOwners: undefined,
    targets: records,
    unchanged: false,
  }
  const resolve = (edge: Edge): unknown => (isNode(edge) ? run.targets[edge.node] : atomValue(edge))
  const compare: Compare = (actual, wanted) =>
    isNode(wanted) ? actual === run.targets[wanted.node] : Object.is(actual, atomValue(wanted))
  const owner = (child: object, kind: symbol): object | undefined =>
    ownersIn(types, records, run, kind).get(child)
  let passes: Passes | undefined
  for (;;) {
    const kept = decide(records, domains, graph.reads, passes)
    if (kept[0] === undefined) return false
    const targets = allocate(types, records, kept)
    if (targets === undefined) return false
    run.targets = targets
    run.nativeOwners = undefined
    const blocked = write(types, graph, domains, kept, run, note, passes, resolve, compare, owner)
    if (blocked === REJECTED) return false
    if (blocked === undefined) return true
    passes = remember(records, kept, targets, blocked, passes)
  }
}

// The owner of each native child of one kind among the targets of the pass; URL child identity
// is fixed for its owner's lifetime, so the lookup performs no live read.
function ownersIn(
  types: PublicationRegistry,
  records: readonly CapturedNode[],
  run: Run,
  kind: symbol,
): WeakMap<object, object> {
  let owners = run.nativeOwners?.get(kind)
  if (owners === undefined) {
    owners = ownersOf(types, records, run.targets, kind)
    ;(run.nativeOwners ??= new Map()).set(kind, owners)
  }
  return owners
}

/**
 * The target of each node: the object it keeps, or a new object allocated in construction order,
 * after the targets it is built from; the kept objects themselves when every node keeps one.
 * Undefined when no order exists or an allocation fails.
 */
function allocate(
  types: PublicationRegistry,
  records: readonly CapturedNode[],
  kept: ReadonlyArray<object | undefined>,
): readonly object[] | undefined {
  const size = records.length
  let fresh = false
  for (let index = 0; index < size; index += 1) if (kept[index] === undefined) fresh = true
  if (!fresh) return kept as readonly object[]
  const targets = denseArray<object>(size)
  const retained = denseArray<boolean>(size)
  for (let index = 0; index < size; index += 1) {
    const target = kept[index]
    retained[index] = target !== undefined
    if (target !== undefined) targets[index] = target
  }
  // Construction dependencies are sealed facts.
  const order = constructionOrder(
    records.map((node) => constructionDependencies(types, node)),
    retained,
  )
  if (order === undefined) return undefined
  // Native ownership found while allocating; a literal holds the field as its own data.
  const owners: NativeOwners = { nativeOwners: undefined }
  const resolve = (edge: Edge): unknown => (isNode(edge) ? targets[edge.node] : atomValue(edge))
  for (let position = 0; position < order.length; position += 1) {
    const index = order[position]
    const target = types.policies[records[index].layout.kind].allocate(
      records[index],
      resolve,
      owners,
    )
    if (target === undefined) return undefined
    targets[index] = target
  }
  return targets
}

// The owner of each native child among the targets of one kind: the target whose construction
// edge names the child, which is the child's target.
function ownersOf(
  types: PublicationRegistry,
  records: readonly CapturedNode[],
  targets: readonly object[],
  kind: symbol,
): WeakMap<object, object> {
  const owners = new WeakMap<object, object>()
  const bindings = types.policies[kind].bindings
  if (bindings.tag !== 'dependent') return owners
  for (let index = 0; index < records.length; index += 1) {
    const node = records[index]
    if (node.pinned !== undefined || node.layout.kind !== kind) continue
    const edges = bindings.read(node, targets[index])
    for (let edge = 0; edge < edges.length; edge += 1)
      if (edges[edge].identity === targets[edges[edge].node])
        owners.set(edges[edge].identity, targets[index])
  }
  return owners
}

/** A new object refused a write, which nothing else has seen, so no pass can repair it. */
const REJECTED = 'rejected'
/** Every publication of the pass wrote nothing that a readback would reject. */
const WRITE_FREE = 'write-free'

/**
 * Writes one pass: publishes every unpinned node and reads the written objects back. Returns the
 * blocked objects, undefined when there are none, or `REJECTED`.
 */
function write(
  types: PublicationRegistry,
  graph: CapturedGraph,
  domains: Candidates,
  kept: ReadonlyArray<object | undefined>,
  run: Run,
  note: PublicationNote,
  passes: Passes | undefined,
  resolve: (edge: Edge) => unknown,
  compare: Compare,
  owner: (child: object, kind: symbol) => object | undefined,
): object[] | typeof REJECTED | undefined {
  const published = publishAll(types, graph, domains, kept, run, note, passes, resolve, owner)
  if (published === REJECTED) return REJECTED
  // A first pass that wrote nothing that a readback would reject is done: no setter or trap ran,
  // so each readback would observe what publication compared (Property.WriteFreeReadback). A
  // retry follows the call's own writes and is always read back (acceptsRetry).
  if (published === WRITE_FREE && passes === undefined) return undefined
  return readback(
    types,
    graph.nodes,
    kept,
    run.targets,
    compare,
    published === WRITE_FREE ? undefined : published,
  )
}

/**
 * Publishes every unpinned node of a pass, new objects first: code that a write into a kept object
 * runs, such as a setter, finds each new object complete. Returns the objects whose preflight or
 * write was refused, undefined when there are none, `REJECTED` or `WRITE_FREE`.
 */
function publishAll(
  types: PublicationRegistry,
  graph: CapturedGraph,
  domains: Candidates,
  kept: ReadonlyArray<object | undefined>,
  run: Run,
  note: PublicationNote,
  passes: Passes | undefined,
  resolve: (edge: Edge) => unknown,
  owner: (child: object, kind: symbol) => object | undefined,
): object[] | typeof REJECTED | typeof WRITE_FREE | undefined {
  run.unchanged = true
  const fresh = publishPhase(types, graph, domains, kept, run, note, passes, resolve, owner, true)
  if (fresh === REJECTED) return REJECTED
  const blocked = publishPhase(
    types,
    graph,
    domains,
    kept,
    run,
    note,
    passes,
    resolve,
    owner,
    false,
  )
  note.facts = undefined
  note.reads = undefined
  return run.unchanged ? WRITE_FREE : blocked
}

// Publishes the new or the kept unpinned nodes of a pass. Returns the kept objects whose
// preflight or write was refused, undefined when there are none, or `REJECTED` when a new object
// refused a write.
function publishPhase(
  types: PublicationRegistry,
  graph: CapturedGraph,
  domains: Candidates,
  kept: ReadonlyArray<object | undefined>,
  run: Run,
  note: PublicationNote,
  passes: Passes | undefined,
  resolve: (edge: Edge) => unknown,
  owner: (child: object, kind: symbol) => object | undefined,
  fresh: boolean,
): object[] | typeof REJECTED | undefined {
  const records = graph.nodes
  let blocked: object[] | undefined
  for (let index = 0; index < records.length; index += 1) {
    const target = kept[index]
    if (records[index].pinned !== undefined || (target === undefined) !== fresh) continue
    note.unchanged = false
    const accepted = publishNode(
      types,
      graph,
      domains,
      index,
      fresh,
      run,
      note,
      passes,
      resolve,
      owner,
    )
    if (!note.unchanged) run.unchanged = false
    if (accepted) continue
    if (target === undefined) return REJECTED
    ;(blocked ??= []).push(target)
  }
  return blocked
}

// Publishes one node into its target, after preparing a kept target; whether the preflight and
// the write were accepted.
function publishNode(
  types: PublicationRegistry,
  graph: CapturedGraph,
  domains: Candidates,
  index: number,
  fresh: boolean,
  run: Run,
  note: PublicationNote,
  passes: Passes | undefined,
  resolve: (edge: Edge) => unknown,
  owner: (child: object, kind: symbol) => object | undefined,
): boolean {
  const target = run.targets[index]
  if (fresh) {
    note.facts = undefined
    note.reads = undefined
  } else if (!prepareKept(types, graph, domains, index, target, note, passes)) return false
  const node = graph.nodes[index]
  return types.policies[node.layout.kind].publish(node, target, resolve, owner, note)
}

/**
 * Gives the publication of a kept object its reads and facts: in the first pass, what capture or
 * discovery read at its slots and the preflight's facts; in a later pass, after this call's own
 * writes, what the previous pass read back of it, which is what that pass wanted, and a preflight
 * run again. False when that preflight fails.
 */
function prepareKept(
  types: PublicationRegistry,
  graph: CapturedGraph,
  domains: Candidates,
  index: number,
  target: object,
  note: PublicationNote,
  passes: Passes | undefined,
): boolean {
  const node = graph.nodes[index]
  if (passes?.writtenAt[index] !== target) {
    note.reads = alignedReads(graph, index, target)
    if (passes === undefined) {
      note.facts = candidateOf(domains[index], target)?.facts
      return true
    }
  } else note.reads = wantedReads(node, passes.previousTargets)
  note.prototype = undefined
  note.facts = undefined
  return types.policies[node.layout.kind].requirements(node, target, note) !== undefined
}

// The value the previous pass wanted at each edge of `node`, which its readback saw there.
function wantedReads(node: CapturedNode, targets: readonly object[]): unknown[] {
  const edges = node.edges
  const reads = denseArray<unknown>(edges.length)
  for (let index = 0; index < edges.length; index += 1) {
    const edge = edges[index]
    reads[index] = isNode(edge) ? targets[edge.node] : atomValue(edge)
  }
  return reads
}

/**
 * Reads every unpinned node back after a pass's writes. A kept object that does not hold its
 * node's contents is blocked, added to `blocked` unless the pass already found it so. Returns the
 * blocked objects, undefined when there are none, or `REJECTED` when a new object does not hold
 * its contents, which no further pass can repair.
 */
function readback(
  types: PublicationRegistry,
  records: readonly CapturedNode[],
  kept: ReadonlyArray<object | undefined>,
  targets: readonly object[],
  compare: Compare,
  blocked: object[] | undefined,
): object[] | typeof REJECTED | undefined {
  const found = blocked?.length ?? 0
  for (let index = 0; index < records.length; index += 1) {
    const node = records[index]
    if (node.pinned !== undefined) continue
    const target = targets[index]
    const fresh = kept[index] === undefined
    if (
      matchesKind(types, target, node.layout.kind) &&
      types.policies[node.layout.kind].matches(node, target, compare)
    )
      continue
    if (fresh) return REJECTED
    if (!blockedAlready(blocked, found, target)) (blocked ??= []).push(target)
  }
  return blocked
}

// Whether the pass found `target` blocked before its readback.
function blockedAlready(
  blocked: readonly object[] | undefined,
  found: number,
  target: object,
): boolean {
  for (let index = 0; index < found; index += 1) if (blocked![index] === target) return true
  return false
}

// Records what a pass leaves for the next: the objects it found blocked are forbidden, and the
// objects it wrote stay at their nodes.
function remember(
  records: readonly CapturedNode[],
  kept: ReadonlyArray<object | undefined>,
  targets: readonly object[],
  blocked: readonly object[],
  passes: Passes | undefined,
): Passes {
  const state: Passes = passes ?? {
    forbidden: new Set(),
    previousTargets: targets,
    written: new Map(),
    writtenAt: denseArray<object | undefined>(records.length),
  }
  state.previousTargets = targets
  for (let index = 0; index < blocked.length; index += 1) state.forbidden.add(blocked[index])
  for (let index = 0; index < records.length; index += 1) {
    const target = records[index].pinned === undefined ? kept[index] : undefined
    state.writtenAt[index] = target
    if (target !== undefined) state.written.set(target, index)
  }
  return state
}
