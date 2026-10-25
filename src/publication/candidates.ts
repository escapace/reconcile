import { isNode } from '../graph/edge'
import { matchesKind, recognize } from '../adapters/recognition'
import { isObject } from '../object-property'
import { ownValue } from '../types/shared/properties'
import { EMPTY_FACTS, UNREAD } from '../constants'
import type {
  Candidate,
  Candidates,
  CapturedGraph,
  CapturedNode,
  Edge,
  PublicationNote,
  PublicationRegistry,
  SlotRead,
} from '../types'
import { denseArray } from '../standard-prototypes'
import { tableOf } from './capture'

/**
 * Discovers the candidates of every node: the aligned current objects of its kind that pass the
 * preflight, in discovery order, each with the objects its fixed slots require other nodes to
 * keep. The root's only candidate is `root`; a pinned node's is itself. Nothing is selected or
 * written here (Spec.Reconcile.discover).
 */
export function candidates(
  types: PublicationRegistry,
  records: readonly CapturedNode[],
  root: object,
  alignment?: Pick<
    CapturedGraph,
    | 'alignedAt'
    | 'candidateReads'
    | 'currents'
    | 'firstAligned'
    | 'firstAlignedAt'
    | 'kinds'
    | 'occupants'
    | 'pinned'
    | 'prototypes'
    | 'reads'
    | 'sources'
  >,
  note?: PublicationNote,
): Candidates {
  const aligned = collect(types, root, records, alignment)
  // Objects inside pinned subtrees stay untouched, so no other position may retain one, and
  // a captured node whose own object lies inside one is already published: it is pinned to
  // itself, which keeps sharing across the boundary. Every kind converts: a view's buffer
  // edge still resolves through its own pinned node, and construction inputs were already
  // read during capture. The root is exempt: a reference to the current root is the live root.
  const walked = alignment?.pinned
  const pinned = walked !== undefined && walked.size !== 0 ? walked : undefined
  if (pinned !== undefined) {
    const sources = alignment?.sources
    records.forEach((node, index) => {
      if (index === 0 || node.pinned !== undefined) return
      const source = sources?.[index]
      if (source !== undefined && source !== root && pinned.has(source))
        (node as { pinned?: object }).pinned = source
    })
    // No new URL can own `searchParams` that stay in place, so their URL is kept as it is.
    for (let index = 1; index < records.length; index += 1)
      if (records[index].pinned === undefined && ownsPinned(types, records, index))
        (records[index] as { pinned?: object }).pinned = sources![index]
  }
  // A candidate that passes the preflight, or undefined when it cannot be kept.
  const admitted = (
    node: CapturedNode,
    index: number,
    candidate: object,
    policy: PublicationRegistry['policies'][symbol],
  ): Candidate | undefined => {
    const prototype = ingressOf(types, node, index, candidate, alignment)
    if (prototype === MISMATCH) return undefined
    if (index !== 0 && pinned?.has(candidate) === true) return undefined
    // What capture or discovery read at the candidate's slots serves its fixed slots.
    const reads = alignedReads(alignment, index, candidate)
    const required = preflightOf(policy, node, candidate, note, prototype, reads)
    if (required === undefined) return undefined
    // The candidate's facts serve the publication that keeps it.
    return { facts: note?.facts, identity: candidate, required }
  }
  const domains = records.map((node, index): Candidate[] => {
    if (node.pinned !== undefined)
      return [{ facts: undefined, identity: node.pinned, required: EMPTY_FACTS }]
    const policy = types.policies[node.layout.kind]
    const list = index === 0 ? undefined : aligned[index]
    const count = index === 0 ? 1 : list === undefined ? 0 : list.length
    // At most one candidate per aligned object, written in place and trimmed.
    const choices = denseArray<Candidate>(count)
    let written = 0
    for (let at = 0; at < count; at += 1) {
      const choice = admitted(node, index, index === 0 ? root : list![at], policy)
      if (choice !== undefined) choices[written++] = choice
    }
    if (written !== choices.length) choices.length = written
    return choices
  })
  for (let owner = 0; owner < records.length; owner += 1)
    keepWithOwner(types, records, domains, owner)
  promoteDemanded(domains)
  return domains
}

// The children an owner kind creates, a URL's `searchParams`, at `node`; empty for other kinds.
function ownedChildren(types: PublicationRegistry, node: CapturedNode): readonly number[] {
  const bindings = types.policies[node.layout.kind].bindings
  return bindings.tag === 'dependent' && bindings.owns === true
    ? bindings.dependencies(node)
    : EMPTY_FACTS
}

// Whether a child that the node at `index` creates is pinned.
function ownsPinned(
  types: PublicationRegistry,
  records: readonly CapturedNode[],
  index: number,
): boolean {
  const children = ownedChildren(types, records[index])
  for (let at = 0; at < children.length; at += 1)
    if (records[children[at]].pinned !== undefined) return true
  return false
}

// Each object that a candidate in `domain` requires at node `child`, mapped to that candidate.
function ownersAt(domain: readonly Candidate[], child: number): Map<object, object> {
  const owners = new Map<object, object>()
  for (let index = 0; index < domain.length; index += 1) {
    const required = domain[index].required
    for (let edge = 0; edge < required.length; edge += 1)
      if (required[edge].node === child) owners.set(required[edge].identity, domain[index].identity)
  }
  return owners
}

/**
 * Keeps each child that the node at `owner` creates only together with its owner: a candidate of
 * the child must be the child of a candidate of the owner node, which the decision must keep
 * with it. A new owner creates new children, so an owner node that keeps no current object
 * leaves its children none either.
 */
function keepWithOwner(
  types: PublicationRegistry,
  records: readonly CapturedNode[],
  domains: Candidate[][],
  owner: number,
): void {
  if (records[owner].pinned !== undefined) return
  const children = ownedChildren(types, records[owner])
  for (let at = 0; at < children.length; at += 1) {
    const child = children[at]
    const owners = ownersAt(domains[owner], child)
    const kept: Candidate[] = []
    const choices = domains[child]
    for (let index = 0; index < choices.length; index += 1) {
      const identity = owners.get(choices[index].identity)
      if (identity !== undefined)
        kept.push({
          facts: choices[index].facts,
          identity: choices[index].identity,
          required: [...choices[index].required, { identity, node: owner }],
        })
    }
    domains[child] = kept
  }
}

/**
 * Orders each node's candidates for the decision: first those an admitted candidate of some node
 * requires there, then the rest, each in discovery order. A fixed slot of a kept object must hold
 * the object the decision keeps at its node, so keeping what it holds keeps the slot's owner too
 * (Spec.Reconcile.orderedCandidates).
 */
function promoteDemanded(domains: Candidate[][]): void {
  const demanded = demandedObjects(domains)
  if (demanded === undefined) return
  for (let node = 0; node < domains.length; node += 1) {
    const wanted = demanded[node]
    if (wanted !== undefined) domains[node] = promoted(domains[node], wanted)
  }
}

// The objects the candidates' fixed slots require at each node that has a choice; undefined
// when none. A candidate's demand on its own node for another object is left out: the candidate
// could never be kept with it, so it does not reorder that node (Spec.Reconcile.demands).
function demandedObjects(domains: Candidates): Array<Set<object> | undefined> | undefined {
  let demanded: Array<Set<object> | undefined> | undefined
  for (let node = 0; node < domains.length; node += 1) {
    const domain = domains[node]
    for (let at = 0; at < domain.length; at += 1) {
      const required = domain[at].required
      for (let edge = 0; edge < required.length; edge += 1) {
        const target = required[edge].node
        if (target === node && required[edge].identity !== domain[at].identity) continue
        if (domains[target].length > 1)
          ((demanded ??= denseArray<Set<object> | undefined>(domains.length))[target] ??=
            new Set()).add(required[edge].identity)
      }
    }
  }
  return demanded
}

// The candidates with those in `wanted` first, each part in its order.
function promoted(domain: readonly Candidate[], wanted: ReadonlySet<object>): Candidate[] {
  const ordered: Candidate[] = []
  for (let at = 0; at < domain.length; at += 1)
    if (wanted.has(domain[at].identity)) ordered.push(domain[at])
  for (let at = 0; at < domain.length; at += 1)
    if (!wanted.has(domain[at].identity)) ordered.push(domain[at])
  return ordered
}

/**
 * What the call read at the slots of `candidate` for node `index` before any write: the occupants
 * capture recorded for the object it aligned, or the values discovery read for another aligned
 * object (WriteFreeReadback.publishPre). Discovery reads every slot of a candidate it walks, so
 * its first publication reads nothing it already read.
 */
export const alignedReads = (
  alignment: Pick<CapturedGraph, 'candidateReads' | 'currents' | 'occupants'> | undefined,
  index: number,
  candidate: unknown,
): readonly unknown[] | undefined =>
  !isObject(candidate) || alignment === undefined
    ? undefined
    : candidate === alignment.currents?.[index]
      ? alignment.occupants?.[index]
      : alignment.candidateReads?.[index]?.get(candidate)

// A candidate of another kind than its node's.
const MISMATCH: object = /* @__PURE__ */ Object.freeze(Object.create(null) as object)

// Capture recognized the object it aligned with a node as the node's kind and kept the prototype it
// read, or undefined; any other candidate's kind is checked here (Types.Ingress).
function ingressOf(
  types: PublicationRegistry,
  node: CapturedNode,
  index: number,
  candidate: object,
  alignment: Pick<CapturedGraph, 'currents' | 'prototypes'> | undefined,
): object | null | undefined {
  if (candidate === alignment?.currents?.[index]) return alignment.prototypes?.[index]
  return matchesKind(types, candidate, node.layout.kind) ? undefined : MISMATCH
}

// Runs one candidate's preflight; the facts it leaves in `note` belong to this candidate alone.
function preflightOf(
  policy: PublicationRegistry['policies'][symbol],
  node: CapturedNode,
  candidate: object,
  note: PublicationNote | undefined,
  prototype: object | null | undefined,
  reads: readonly unknown[] | undefined,
): ReturnType<PublicationRegistry['policies'][symbol]['requirements']> {
  if (note !== undefined) {
    note.facts = undefined
    note.prototype = prototype
    note.reads = reads
  }
  return policy.requirements(node, candidate, note)
}

// Recorded occupants follow the node edges by position; capture read one for every node edge.
function replayOccupants(
  node: CapturedNode,
  slots: readonly unknown[],
  visit: (current: unknown, edge: Edge) => void,
): void {
  const edges = node.edges
  for (let index = 0; index < edges.length; index += 1)
    if (isNode(edges[index])) visit(slots[index], edges[index])
}

// A node visited without an aligned object of its kind; it holds no candidate.
const VISITED: readonly object[] = /* @__PURE__ */ Object.freeze([])

// Adds an aligned object of the node's kind, replacing the empty `VISITED` marker.
function align(aligned: Array<object[] | undefined>, index: number, candidate: object): void {
  const choices = aligned[index]
  if (choices === undefined || choices === VISITED) aligned[index] = [candidate]
  else choices.push(candidate)
}

// Traversal and visitation are graph-owned; native policies only expose aligned slots.
// Aligned objects per node are few, so a small array replaces a Set per node; a visited node
// without one holds the shared empty `VISITED`.
// Pinned nodes are fixed and never aligned; a first visit through the object aligned
// capture already recognized reuses the occupant reads recorded for its edges.
/** The edge of the root node. */
const ROOT_EDGE: Edge = /* @__PURE__ */ Object.freeze({ node: 0 })

/** The alignment facts discovery reads. */
type Alignment = Pick<
  CapturedGraph,
  | 'alignedAt'
  | 'candidateReads'
  | 'currents'
  | 'firstAligned'
  | 'firstAlignedAt'
  | 'kinds'
  | 'occupants'
  | 'reads'
>

// The node capture first aligned with `candidate`, if any.
const alignedAt = (alignment: Alignment, candidate: object): number | undefined =>
  alignment.alignedAt?.get(candidate) ??
  (candidate === alignment.firstAligned ? alignment.firstAlignedAt : undefined)

// The positional reads of `candidate` at the node it was first aligned or walked at: what capture
// read of the object it aligned there, else what discovery's walk there read; undefined when
// nothing was read.
const readsAt = (
  alignment: Alignment,
  candidate: object,
  first: number,
): readonly unknown[] | undefined =>
  (candidate === alignment.currents?.[first] ? alignment.occupants?.[first] : undefined) ??
  alignment.candidateReads?.[first]?.get(candidate)

function collect(
  types: PublicationRegistry,
  old: unknown,
  records: readonly CapturedNode[],
  alignment?: Alignment,
): ReadonlyArray<readonly object[] | undefined> {
  const aligned = denseArray<object[] | undefined>(records.length)
  // Per-call recognition memo for alias visits, created on the first; first visits reuse the
  // capture's recognition, which also recorded each aligned object of another kind.
  let kinds = alignment?.kinds
  const kindOf = (object: object): symbol => {
    let kind = (kinds ??= new Map<object, symbol>()).get(object)
    if (kind === undefined) kinds.set(object, (kind = recognize(types, object)))
    return kind
  }
  const currents = alignment?.currents
  const occupants = alignment?.occupants
  // The candidate whose slots the walk is reading, by node, and the values read so far, created
  // at its first slot; each value serves that candidate's preflight and first publication.
  let reading = -1
  let readingObject: object | undefined
  let read: unknown[] | undefined
  const note = (current: unknown, position: number | undefined): void => {
    if (position === undefined || readingObject === undefined) return
    if (read === undefined) {
      read = []
      const table = (alignment!.candidateReads ??= denseArray(records.length))
      ;(table[reading] ??= new Map()).set(readingObject, read)
    }
    // Slots are read in edge order; one not read holds `UNREAD`, and so does any past the last.
    while (read.length < position) read.push(UNREAD)
    read.push(current)
  }
  // The node discovery first walked each candidate at, when capture aligned none with it, and
  // the reader of shared candidates; both created on the first walk of a candidate.
  let walked: Map<object, number> | undefined
  let readShared: SlotRead | undefined
  // Gives a candidate walked or aligned before the table of its reads so far, and reads every
  // walked candidate through the table it has, so no key of an object walked or aligned at more
  // than one node is read twice; the table can appear while a walk is under way, when a cycle
  // reaches the same candidate again. A candidate walked at the node capture aligned it with,
  // where capture read nothing of it, has no reads to share yet: `note` records this walk's.
  const readerFor = (index: number, candidate: object): SlotRead | undefined => {
    if (alignment === undefined) return undefined
    if (alignment.reads?.has(candidate) !== true) {
      const first = alignedAt(alignment, candidate) ?? walked?.get(candidate)
      if (first === undefined) (walked ??= new Map()).set(candidate, index)
      else {
        const reads = readsAt(alignment, candidate, first)
        if (first !== index || reads !== undefined)
          (alignment.reads ??= new Map()).set(candidate, tableOf(records[first].keys, reads))
      }
    }
    return (readShared ??= (current, key) => {
      const table = alignment.reads?.get(current)
      if (table?.has(key) === true) return table.get(key)
      const value = ownValue(current, key)
      table?.set(key, value)
      return value
    })
  }
  // Walks the aligned slots of `candidate` for node `index`, noting what it reads.
  const walk = (index: number, node: CapturedNode, candidate: object | undefined): void => {
    const outer = reading
    const outerObject = readingObject
    const outerRead = read
    reading = index
    readingObject = alignment === undefined ? undefined : candidate
    read = undefined
    types.policies[node.layout.kind].aligned(
      node,
      candidate,
      visit,
      candidate === undefined ? undefined : readerFor(index, candidate),
    )
    reading = outer
    readingObject = outerObject
    read = outerRead
  }
  const visit = (current: unknown, edge: Edge, position?: number): void => {
    note(current, position)
    if (!isNode(edge)) return
    const index = edge.node
    const node = records[index]
    if (node.pinned !== undefined) return
    // An already aligned pair carries the selected kind. Repeated aliases do
    // not reopen native recognition or observe the same child surface again.
    const choices = aligned[index]
    const object = isObject(current) ? current : undefined
    if (object !== undefined && choices?.includes(object) === true) return
    const first = choices === undefined
    const recorded = first && object !== undefined && object === currents?.[index]
    const candidate =
      recorded || (object !== undefined && kindOf(object) === node.layout.kind) ? object : undefined
    if (candidate !== undefined) align(aligned, index, candidate)
    else if (!first) return
    else aligned[index] = VISITED as object[]
    const slots = recorded ? occupants![index] : undefined
    if (slots === undefined) walk(index, node, candidate)
    else replayOccupants(node, slots, visit)
  }
  visit(old, ROOT_EDGE)
  return aligned
}
