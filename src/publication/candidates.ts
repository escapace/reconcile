import { isNode } from '../graph/edge'
import { matchesKind, recognize } from '../adapters/recognition'
import { storageIdentity } from '../adapters/vue'
import { isObject } from '../object-property'
import { EMPTY_FACTS, UNREAD } from '../constants'
import type {
  CapturedGraph,
  CapturedNode,
  Choice,
  Domains,
  Edge,
  PreflightFacts,
  PublicationNote,
  PublicationRegistry,
} from '../types'
import { denseArray } from '../standard-prototypes'

// This native boundary compiles fixed own references and view construction into
// the same Requires rule. It does not select a target or mutate captured records.
// Labels are the aligned objects themselves; a fresh choice is labelled by its node index,
// which cannot collide with an object. A pinned node has exactly one retained choice.
export function candidates(
  types: PublicationRegistry,
  records: readonly CapturedNode[],
  root: object,
  alignment?: Pick<
    CapturedGraph,
    | 'candidateReads'
    | 'currents'
    | 'kinds'
    | 'occupants'
    | 'protectedStorage'
    | 'prototypes'
    | 'sources'
  >,
  storage: (value: object, prototype?: object | null) => object = storageIdentity,
  note?: PublicationNote,
  preflight?: Array<PreflightFacts | undefined>,
  wrapper: (value: object, prototype?: object | null) => boolean = (value, prototype) =>
    storageIdentity(value, prototype) !== value,
): Domains {
  const aligned = collect(types, root, records, wrapper, alignment)
  // Objects inside pinned subtrees stay untouched, so no other position may retain one, and
  // a captured node whose own object lies inside one is already published: it is pinned to
  // itself, which keeps sharing across the boundary. Every kind converts: a view's buffer
  // edge still resolves through its own pinned node, and construction inputs were already
  // read during capture. The root is exempt: a reference to the current root is the live root.
  const walked = alignment?.protectedStorage
  const protectedStorage = walked !== undefined && walked.size !== 0 ? walked : undefined
  if (protectedStorage !== undefined) {
    const sources = alignment?.sources
    records.forEach((node, index) => {
      if (index === 0 || node.pinned !== undefined) return
      const source = sources?.[index]
      if (source !== undefined && source !== root && protectedStorage.has(storage(source)))
        (node as { pinned?: object }).pinned = source
    })
  }
  // A candidate's retained choice, or undefined when it cannot be retained.
  const retainedChoice = (
    node: CapturedNode,
    index: number,
    candidate: object,
    policy: PublicationRegistry['policies'][symbol],
  ): Choice | undefined => {
    const prototype = ingressOf(types, node, index, candidate, alignment)
    if (prototype === MISMATCH || !policy.compatible(node, candidate)) return undefined
    if (index !== 0 && protectedStorage?.has(storage(candidate, prototype)) === true)
      return undefined
    // What capture or discovery read at the candidate's slots serves its fixed slots.
    const reads = alignedReads(alignment, index, candidate)
    const required = preflightOf(policy, node, candidate, note, prototype, reads)
    if (required === undefined) return undefined
    // The first passing candidate's facts serve the publication that retains it.
    if (note?.facts !== undefined) preflight![index] ??= note.facts
    return { identity: candidate, required, retained: true, storage: storage(candidate, prototype) }
  }
  return records.map((node, index): Choice[] => {
    if (node.pinned !== undefined)
      return [
        {
          identity: node.pinned,
          required: EMPTY_FACTS,
          retained: true,
          storage: storage(node.pinned),
        },
      ]
    const policy = types.policies[node.layout.kind]
    const list = index === 0 ? undefined : aligned[index]
    const count = index === 0 ? 1 : list === undefined ? 0 : list.length
    // At most one choice per candidate plus the fresh one, written in place and trimmed.
    const choices = denseArray<Choice>(index === 0 ? count : count + 1)
    let written = 0
    for (let at = 0; at < count; at += 1) {
      const choice = retainedChoice(node, index, index === 0 ? root : list![at], policy)
      if (choice !== undefined) choices[written++] = choice
    }
    if (index !== 0)
      choices[written++] = {
        identity: index,
        required: EMPTY_FACTS,
        retained: false,
        storage: index,
      }
    if (written !== choices.length) choices.length = written
    return choices
  })
}

/**
 * What the call read at the slots of `candidate` for node `index` before any write: the occupants
 * capture recorded for the object it aligned, or the values discovery read for another aligned
 * object (WriteFreeReadback.publishPre).
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

// The prototype capture read of the object aligned with node `index`, when `candidate` is it.
const capturedPrototype = (
  alignment: Pick<CapturedGraph, 'currents' | 'prototypes'> | undefined,
  index: number,
  candidate: object | undefined,
): object | null | undefined =>
  candidate !== undefined && candidate === alignment?.currents?.[index]
    ? alignment.prototypes?.[index]
    : undefined

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
function collect(
  types: PublicationRegistry,
  old: unknown,
  records: readonly CapturedNode[],
  wrapper: (value: object, prototype?: object | null) => boolean,
  alignment?: Pick<
    CapturedGraph,
    'candidateReads' | 'currents' | 'kinds' | 'occupants' | 'prototypes'
  >,
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
  // Walks the aligned slots of `candidate` for node `index`, noting what it reads.
  const walk = (index: number, node: CapturedNode, candidate: object | undefined): void => {
    const outer = reading
    const outerObject = readingObject
    const outerRead = read
    reading = index
    readingObject = alignment === undefined ? undefined : candidate
    read = undefined
    // A collection asks whether its object is a wrapper, with the prototype capture read, as
    // discovery's later probe of the same object passes it.
    types.policies[node.layout.kind].aligned(
      node,
      candidate,
      visit,
      wrapper,
      capturedPrototype(alignment, index, candidate),
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
  visit(old, { node: 0 })
  return aligned
}
