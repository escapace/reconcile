import { atomValue, isNode } from '../graph/edge'
import { matchesKind } from '../adapters/recognition'
import { EXPOSURE_MODES } from '../constants'
import type {
  Adapter,
  Binding,
  CapturedGraph,
  Choice,
  Domains,
  Edge,
  Execution,
  Selection,
  PublicationRegistry,
  NativeOwners,
  PreflightFacts,
  PublicationNote,
  Readback,
} from '../types'
import { alignedReads, candidates } from './candidates'
import { constructionOrder } from '../graph/construction'
import { constructionDependencies } from '../graph/construction-facts'
import { continueExecution, execute, scoreOf, type HeadOutcome } from '../graph/driver'
import { completeExecution, startExecution } from '../graph/execution'
import { headSelection } from '../graph/selection'
import { denseArray } from '../standard-prototypes'

// Whether no object is a retained choice at two nodes, so that selection need not compare the
// objects of the choices it takes.
function distinctCandidates(domains: Domains): boolean {
  const seen = new Set<unknown>()
  for (let node = 0; node < domains.length; node += 1) {
    const domain = domains[node]
    for (let index = 0; index < domain.length; index += 1) {
      const choice = domain[index]
      if (!choice.retained) continue
      if (seen.has(choice.storage)) return false
      seen.add(choice.storage)
    }
  }
  return true
}

// Claims a fresh target against every old object and the earlier fresh ones; undefined on a
// collision. The set of old objects is built on the first fresh target.
function claimFresh(
  domains: Domains,
  taken: Set<unknown> | undefined,
  target: object,
): Set<unknown> | undefined {
  if (taken === undefined) {
    taken = new Set()
    for (const domain of domains) for (const old of domain) if (old.retained) taken.add(old.storage)
  }
  if (taken.has(target)) return undefined
  taken.add(target)
  return taken
}

// Fixed identities are the root and everything its selected choices pin transitively;
// undefined when the root pins nothing and is the only fixed node.
function fixedNodes(choices: readonly Choice[]): Set<number> | undefined {
  if (choices[0].required.length === 0) return undefined
  const fixed = new Set([0])
  for (const node of fixed) for (const edge of choices[node].required) fixed.add(edge.node)
  return fixed
}

const isFixed = (fixed: ReadonlySet<number> | undefined, index: number): boolean =>
  fixed === undefined ? index === 0 : fixed.has(index)

// Readback results are only read; one frozen match serves every node, one frozen reject every
// failure without a rebind.
const MATCH: Readback = /* @__PURE__ */ Object.freeze({ kind: 'match' })
const REJECT: Readback = /* @__PURE__ */ Object.freeze({ kind: 'reject' })

// After a call's own writes, retained replaceable targets rerun the preflight; the first one
// that no longer passes, or -1. A fresh choice is labelled by its node index; a retained one by
// its object. A fixed slot's value comes from what the previous readback saw of a node it
// matched (`seen`), or is read once and kept in `note.held` for the publication that follows.
function stale(
  state: Execution,
  records: CapturedGraph['nodes'],
  types: PublicationRegistry,
  note: PublicationNote,
  seen: (index: number, binding: Binding) => unknown[] | undefined,
): number {
  let rejected = -1
  for (let index = 0; index < records.length && rejected === -1; index += 1) {
    const binding = state.bindings[index]
    if (typeof binding.choice === 'number' || records[index].pinned !== undefined) continue
    note.prototype = undefined
    note.reads = seen(index, binding)
    if (
      types.policies[records[index].layout.kind].requirements(
        records[index],
        binding.writer as object,
        note,
      ) === undefined
    )
      rejected = index
  }
  note.facts = undefined
  note.reads = undefined
  return rejected
}

// Publishes every node that is not pinned; the first one refused, or -1. New objects are filled
// before kept ones, which link them: code that a write into a kept object runs, such as a setter,
// finds each new object complete.
function publishFreshFirst(
  state: Execution,
  records: CapturedGraph['nodes'],
  publishNode: (index: number) => boolean,
): number {
  for (let pass = 0; pass < 2; pass += 1)
    for (let index = 0; index < records.length; index += 1)
      if (
        records[index].pinned === undefined &&
        (typeof state.bindings[index].choice === 'number') === (pass === 0) &&
        !publishNode(index)
      )
        return index
  return -1
}

/** Reads the live object currently exposed at a node of one attempt. */
const exposed = (state: Execution, index: number): object => state.bindings[index].exposed as object

// The finite driver owns all selection/revision/retry decisions. This adapter
// translates native observations to outcomes without changing an active image.
// Binding labels are the live objects themselves, so no handle table is needed.
// Pinned nodes are retained as they are: no preflight, publication or readback inside.
export function publishGraph(
  types: PublicationRegistry,
  graph: CapturedGraph,
  root: object,
): boolean {
  const records = graph.nodes
  const size = records.length
  const policies = types.policies
  // Construction dependencies are sealed facts, listed on the first preparation.
  let dependencies: Array<readonly number[]> | undefined
  // The channel between this call's preflights and publications, and the facts a passing
  // preflight read, by node.
  const note: PublicationNote = {
    facts: undefined,
    fresh: false,
    held: undefined,
    prototype: undefined,
    reads: undefined,
    unchanged: false,
  }
  const preflight = denseArray<PreflightFacts | undefined>(size)
  const domains = candidates(types, records, root, graph, note, preflight)
  // Retained choices are their objects and fresh ones their own node number, so two choices
  // share a label only when one object is a candidate at two nodes.
  const distinctStorages = distinctCandidates(domains)
  // Binds each selected target to its choice; undefined when a fresh target reuses an old object
  // or a construction edge names another target.
  const bind = (choices: readonly Choice[], targets: readonly object[]): Binding[] | undefined => {
    const fixed = fixedNodes(choices)
    const bindings = denseArray<Binding>(size)
    // A retained target observes its choice's memoized storage, and selection admits no two
    // choices with one storage (GraphPolicy feasible), so only a fresh target can collide: with
    // any old storage, or with an earlier fresh target. A retained target sharing an earlier
    // fresh target's storage was already rejected at that fresh target. The taken set exists
    // only once a fresh target is bound.
    let taken: Set<unknown> | undefined
    for (let index = 0; index < size; index += 1) {
      const target = targets[index]
      const node = records[index]
      const choice = choices[index]
      if (!choice.retained) {
        taken = claimFresh(domains, taken, target)
        if (taken === undefined) return undefined
      }
      // A retained choice's requirements already name the selected targets; dependent
      // construction extends a copy of them with edges that must name the selected targets.
      const construction = policies[node.layout.kind].bindings
      const read = construction.tag === 'dependent' ? construction.read(node, target) : undefined
      if (read?.some((edge) => edge.identity !== targets[edge.node]) === true) return undefined
      bindings[index] = {
        choice: choice.identity,
        construction: read === undefined ? choice.required : [...choice.required, ...read],
        exposed: target,
        fixed: isFixed(fixed, index),
        mode: 0,
        palette: EXPOSURE_MODES,
        storage: target,
        writer: target,
      }
    }
    return bindings
  }
  // The attempt being published or read back; the callbacks below read it instead of closing
  // over each revision.
  let active: Execution | undefined
  const resolve = (edge: Edge): unknown =>
    isNode(edge) ? active!.bindings[edge.node].exposed : atomValue(edge)
  const writer = (index: number): object => active!.bindings[index].writer as object
  // Construction bindings already observed native ownership at prepare. URL child
  // identity is fixed for its owner's lifetime, so this lookup performs no live read.
  let nativeOwners: Map<symbol, WeakMap<object, object>> | undefined
  const owner = (child: object, kind: symbol): object | undefined => {
    let owners = nativeOwners?.get(kind)
    if (owners === undefined) {
      owners = new WeakMap<object, object>()
      ;(nativeOwners ??= new Map()).set(kind, owners)
      for (let index = 0; index < size; index += 1) {
        if (records[index].pinned !== undefined || records[index].layout.kind !== kind) continue
        for (const edge of active!.bindings[index].construction)
          if (edge.identity === writer(edge.node)) owners.set(edge.identity, writer(index))
      }
    }
    return owners.get(child)
  }
  const compare = (actual: unknown, wanted: Edge): boolean =>
    isNode(wanted) ? actual === exposed(active!, wanted.node) : Object.is(actual, atomValue(wanted))
  // Candidate discovery already ran the requirement scan on every retained candidate while no
  // write had happened; it is the preflight. The engine repeats it only after this call's own
  // writes, and never on a fresh target, which is private until it is published.
  let written = false
  // Whether the first publication wrote nothing that a readback would reject: with no write no
  // setter or write trap ran, so each readback would observe what publication compared and
  // accept (Property.WriteFreeReadback), and the engine answers it without reading again.
  let confirmed = false
  // An exception from a setter, trap or method propagates unchanged at any depth, without
  // rollback; only a refusal the publication detects makes the driver try another plan.
  // Publishes one node of the active execution; the first publication passes the preflight's
  // facts along. `unchanged` ends false when any node of a publication wrote.
  let first = false
  let unchanged = false
  // The attempt the last readback read and how many of its nodes, from the first, matched: the
  // readback reads them in order and stops at the first mismatch. Each held what that revision
  // wanted, which a retried publication decides from instead of reading again
  // (WriteFreeReadback.publishSeen); a retry's readback always reads.
  let checked: Execution | undefined
  let matching = 0
  // What the last readback saw at each key of a node it matched, when the node is published
  // through the object that readback read.
  const seen = (index: number, binding: Binding): unknown[] | undefined => {
    const before = checked === undefined || index >= matching ? undefined : checked.bindings[index]
    if (before?.choice !== binding.choice || before.exposed !== binding.writer) return undefined
    const edges = records[index].edges
    const reads = denseArray<unknown>(edges.length)
    for (let edge = 0; edge < edges.length; edge += 1) {
      const wanted = edges[edge]
      reads[edge] = isNode(wanted) ? checked!.bindings[wanted.node].exposed : atomValue(wanted)
    }
    return reads
  }
  const publishNode = (index: number): boolean => {
    const binding = active!.bindings[index]
    // Facts serve only the object they were read from.
    const facts = preflight[index]
    note.facts = first && facts?.current === binding.choice ? facts : undefined
    note.unchanged = false
    note.fresh = typeof binding.choice === 'number'
    // What capture or discovery read at the object's slots serves its first publication.
    note.reads = first ? alignedReads(graph, index, binding.choice) : seen(index, binding)
    const node = records[index]
    const accepted = policies[node.layout.kind].publish(
      node,
      binding.writer as object,
      resolve,
      owner,
      note,
    )
    if (!note.unchanged) unchanged = false
    return accepted
  }
  const prepare = (selection: Selection): Binding[] | undefined => {
    const choices = denseArray<Choice>(size)
    const targets = denseArray<object>(size)
    let fresh = false
    for (let node = 0; node < size; node += 1) {
      const choice = domains[node][selection[node]]
      choices[node] = choice
      targets[node] = choice.retained ? (choice.identity as object) : (undefined as never)
      if (!choice.retained) fresh = true
    }
    // With every choice retained the construction order is empty.
    if (fresh) {
      dependencies ??= records.map((node) => constructionDependencies(types, node))
      const order = constructionOrder(
        dependencies,
        choices.map((choice) => choice.retained),
      )
      if (order === undefined) return undefined
      // Native ownership found while allocating; a literal holds the field as its own data.
      const owners: NativeOwners = { nativeOwners: undefined }
      const resolveTarget = (edge: Edge): unknown =>
        isNode(edge) ? targets[edge.node] : atomValue(edge)
      for (let position = 0; position < order.length; position += 1) {
        const index = order[position]
        const target = policies[records[index].layout.kind].allocate(
          records[index],
          resolveTarget,
          owners,
        )
        if (target === undefined) return undefined
        targets[index] = target
      }
    }
    return bind(choices, targets)
  }
  const publish = (state: Execution): ReturnType<Adapter['publish']> => {
    active = state
    nativeOwners = undefined
    // Each later publication decides from reads made after the previous one's writes.
    if (written) note.held = undefined
    const rejected = written ? stale(state, records, types, note, seen) : -1
    if (rejected !== -1) return { rejected }
    // Only the first publication reads the preflight's facts and may confirm itself: its
    // targets are the ones the preflight read, and each is exposed as it is written.
    first = !written
    written = true
    confirmed = false
    unchanged = first
    const refused = publishFreshFirst(state, records, publishNode)
    note.facts = undefined
    note.fresh = false
    note.reads = undefined
    // A refused publication wrote without a readback after it; the next one reads afresh.
    checked = refused === -1 ? state : undefined
    matching = 0
    if (refused !== -1) return { rejected: refused }
    confirmed = unchanged
    return true
  }
  const readback = (state: Execution, index: number): Readback => {
    const node = records[index]
    if (node.pinned !== undefined || confirmed) {
      matching = index + 1
      return MATCH
    }
    const target = exposed(state, index)
    active = state
    const matches =
      matchesKind(types, target, node.layout.kind) &&
      policies[node.layout.kind].matches(
        node,
        target,
        compare,
        typeof state.bindings[index].choice === 'number' && target === writer(index),
      )
    if (!matches) return REJECT
    matching = index + 1
    return MATCH
  }
  // The driver's adapter, built only when the driver takes over from the head attempt.
  const adapter = (): Adapter & { retention: (state: Execution) => number } => ({
    prepare,
    publish,
    readback,
    retention(state) {
      let score = 0
      for (let index = 0; index < size; index += 1) {
        const target = exposed(state, index)
        // A retained choice is labelled by its own identity, so exposing it scores without
        // searching its domain.
        if (state.bindings[index].choice === target) {
          score += 1
          continue
        }
        const domain = domains[index]
        for (let choice = 0; choice < domain.length; choice += 1)
          if (domain[choice].retained && domain[choice].identity === target) {
            score += 1
            break
          }
      }
      return score
    },
  })
  // The head plan's first revision runs here, with the adapter's callbacks called directly;
  // the driver continues from any other outcome exactly as its own first attempt would.
  const head = headSelection(domains, distinctStorages)
  if (head === undefined) return execute(domains, adapter(), distinctStorages).kind === 'accepted'
  const bindings = prepare(head)
  if (bindings?.length !== size) return afterHead(domains, adapter(), head, UNPREPARED)
  // The head attempt is plan 0; the driver numbers its own attempts from 1.
  const state = startExecution(0, bindings)
  const publication = publish(state)
  if (publication !== true)
    return afterHead(domains, adapter(), head, { publication, tag: 'refused' })
  let node = 0
  let result: Readback = MATCH
  for (; node < size; node += 1) {
    result = readback(state, node)
    if (result.kind !== 'match') break
  }
  // A first revision whose readbacks all match is done with its bindings unchanged
  // (Execution.check_all_done), so every node exposes its prepared target, a retained choice's
  // own identity: an all-retained head scores its upper bound, as the retention scan would.
  if (result.kind === 'match' && scoreOf(domains, head) === size) return true
  return afterHead(domains, adapter(), head, headResult(state, node, result))
}

const UNPREPARED: HeadOutcome = /* @__PURE__ */ Object.freeze({ tag: 'unprepared' })

function headResult(state: Execution, node: number, result: Readback): HeadOutcome {
  return result.kind === 'match'
    ? { state: completeExecution(state), tag: 'done' }
    : { node, result, state, tag: 'mismatch' }
}

function afterHead(
  domains: Domains,
  adapter: Adapter,
  head: Selection,
  outcome: HeadOutcome,
): boolean {
  return continueExecution(domains, adapter, head, outcome).kind === 'accepted'
}
