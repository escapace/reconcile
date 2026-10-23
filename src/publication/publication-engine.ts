import { atomValue, isNode } from '../graph/edge'
import { matchesKind, recognize } from '../adapters/recognition'
import { ExposurePalette, storageIdentity } from '../adapters/vue'
import { EXPOSURE_MODES } from '../constants'
import { isObject } from '../object-property'
import type {
  Adapter,
  Binding,
  CapturedGraph,
  Choice,
  Domains,
  Edge,
  Execution,
  ExposureObservation,
  Selection,
  PublicationRegistry,
  NativeOwners,
  PreflightFacts,
  PublicationNote,
  Readback,
} from '../types'
import { candidates } from './candidates'
import { constructionOrder } from '../graph/construction'
import { constructionDependencies } from '../graph/construction-facts'
import { continueExecution, execute, scoreOf, type HeadOutcome } from '../graph/driver'
import { completeExecution, startExecution } from '../graph/execution'
import { headSelection } from '../graph/selection'
import { denseArray } from '../standard-prototypes'

// Claims a fresh target's storage against every old storage and the earlier fresh ones;
// undefined on a collision. The set of old storages is built on the first fresh target.
function claimFresh(
  domains: Domains,
  taken: Set<unknown> | undefined,
  storage: object,
): Set<unknown> | undefined {
  if (taken === undefined) {
    taken = new Set()
    for (const domain of domains) for (const old of domain) if (old.retained) taken.add(old.storage)
  }
  if (taken.has(storage)) return undefined
  taken.add(storage)
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
  // Storage identity is stable for the duration of one call; probe each object once. While no
  // probe repeats an object or resolves a wrapper, every probed object is its own storage and
  // no two probes share one.
  const storages = new Map<object, object>()
  let unshared = true
  const storage = (value: object, prototype?: object | null): object => {
    let owner = storages.get(value)
    if (owner === undefined) {
      storages.set(value, (owner = storageIdentity(value, prototype)))
      if (owner !== value) unshared = false
    } else unshared = false
    return owner
  }
  // The channel between this call's preflights and publications, and the facts a passing
  // preflight read, by node.
  const note: PublicationNote = { facts: undefined, prototype: undefined, unchanged: false }
  const preflight = denseArray<PreflightFacts | undefined>(size)
  const domains = candidates(types, records, root, graph, storage, note, preflight)
  // Retained choices take their storage from these probes and fresh ones their own node number,
  // so when discovery shared nothing no two choices share storage.
  const distinctStorages = unshared
  // Created on the first wrapper: an ordinary object is its own storage and its own mode-0
  // handle, which the palette would answer without recording it.
  let palette: ExposurePalette | undefined
  const observe = (value: object, kind: symbol): ExposureObservation | undefined =>
    storage(value) === value
      ? { mode: 0, storage: value }
      : (palette ??= new ExposurePalette(
          (wrapper) => types.exposures[recognize(types, wrapper)],
          storage,
        )).observe(value, types.exposures[kind])
  // Observes each selected target once and binds it to its choice; undefined when two
  // targets share storage, a fresh target reuses old storage or a construction edge names
  // another target.
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
      const observed = observe(target, node.layout.kind)
      if (observed === undefined) return undefined
      if (!choice.retained) {
        taken = claimFresh(domains, taken, observed.storage)
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
        mode: observed.mode,
        palette: EXPOSURE_MODES,
        storage: observed.storage,
        writer: target,
      }
    }
    return bindings
  }
  // The attempt being published or read back; the callbacks below read it instead of closing
  // over each revision.
  let active: Execution | undefined
  const resolve = (edge: Edge): unknown =>
    isNode(edge) ? exposed(active!, edge.node) : atomValue(edge)
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
  // The rebind the current readback comparison found, if any.
  let outcome: Readback = REJECT
  const compare = (actual: unknown, wanted: Edge): boolean => {
    if (!isNode(wanted)) return Object.is(actual, atomValue(wanted))
    const state = active!
    const child = wanted.node
    if (actual === exposed(state, child)) return true
    if (isObject(actual) && storage(actual) === state.bindings[child].storage) {
      const observed = observe(actual, records[child].layout.kind)
      if (observed !== undefined)
        outcome = {
          exposed: actual,
          kind: 'rebind',
          mode: observed.mode,
          node: child,
          storage: observed.storage,
        }
    }
    return false
  }
  // Candidate discovery already ran the requirement scan on every retained candidate while no
  // write had happened; it is the preflight. The engine repeats it only after this call's own
  // writes, and never on a fresh target, which is private until it is published.
  let written = false
  // Whether the first publication wrote nothing that a readback would reject: with no write no
  // setter or write trap ran, so each readback would observe what publication compared and
  // accept (Property.WriteFreeReadback), and the engine answers it without reading again.
  let confirmed = false
  // Recover only native publication exceptions on replaceable nodes. A fixed receiver's host
  // exception remains a public failure, without rollback.
  const publishNode = (state: Execution, index: number): boolean => {
    const node = records[index]
    try {
      return policies[node.layout.kind].publish(node, writer(index), resolve, owner, note)
    } catch (error) {
      if (state.bindings[index].fixed) throw error
      return false
    }
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
    // After this call's own writes, retained replaceable targets rerun the preflight. A fresh
    // choice is labelled by its node index; a retained one by its object.
    for (let index = 0; index < size; index += 1)
      if (
        written &&
        typeof state.bindings[index].choice !== 'number' &&
        records[index].pinned === undefined &&
        policies[records[index].layout.kind].requirements(records[index], writer(index)) ===
          undefined
      )
        return { rejected: index }
    // Only the first publication reads the preflight's facts and may confirm itself: its
    // targets are the ones the preflight read, and each is exposed as it is written.
    const first = !written
    written = true
    confirmed = false
    let unchanged = first
    for (let index = 0; index < size; index += 1) {
      if (records[index].pinned !== undefined) continue
      // Facts serve only the object they were read from, exposed as itself; a wrapper's
      // descriptors hold its raw contents, so it reads its own.
      const facts = preflight[index]
      note.facts =
        first && facts?.current === state.bindings[index].choice && state.bindings[index].mode === 0
          ? facts
          : undefined
      note.unchanged = false
      if (!publishNode(state, index)) return { rejected: index }
      if (!note.unchanged) unchanged = false
    }
    note.facts = undefined
    confirmed = unchanged
    return true
  }
  const readback = (state: Execution, index: number): Readback => {
    const node = records[index]
    // Bind and rebind store the memoized storage of the exposed object, so it always equals
    // the binding's storage here, and no storage check is needed.
    if (node.pinned !== undefined || confirmed) return MATCH
    const target = exposed(state, index)
    active = state
    outcome = REJECT
    const matches =
      matchesKind(types, target, node.layout.kind) &&
      policies[node.layout.kind].matches(node, target, compare)
    return matches ? MATCH : outcome
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
