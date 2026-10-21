import { isNode } from '../graph/edge'
import { matchesKind, recognize } from '../adapters/recognition'
import { storageIdentity } from '../adapters/vue'
import { isObject } from '../object-property'
import { EMPTY_FACTS } from '../constants'
import type {
  CapturedGraph,
  CapturedNode,
  Choice,
  Domains,
  Edge,
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
  alignment?: Pick<CapturedGraph, 'currents' | 'occupants' | 'protectedStorage' | 'sources'>,
  storage: (value: object) => object = storageIdentity,
): Domains {
  const aligned = collect(types, root, records, alignment)
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
    const choices: Choice[] = []
    for (const candidate of index === 0 ? [root] : (aligned[index] ?? [])) {
      if (!matchesKind(types, candidate, node.layout.kind) || !policy.compatible(node, candidate))
        continue
      if (index !== 0 && protectedStorage?.has(storage(candidate)) === true) continue
      const required = policy.requirements(node, candidate)
      if (required === undefined) continue
      choices.push({
        identity: candidate,
        required,
        retained: true,
        storage: storage(candidate),
      })
    }
    if (index !== 0)
      choices.push({ identity: index, required: EMPTY_FACTS, retained: false, storage: index })
    return choices
  })
}

// Recorded occupants follow the node edges in order; atom edges have no entry.
function replayOccupants(
  node: CapturedNode,
  slots: readonly unknown[],
  visit: (current: unknown, edge: Edge) => void,
): void {
  let slot = 0
  for (const child of node.edges) if (isNode(child)) visit(slots[slot++], child)
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
  alignment?: Pick<CapturedGraph, 'currents' | 'occupants'>,
): ReadonlyArray<readonly object[] | undefined> {
  const aligned = denseArray<object[] | undefined>(records.length)
  // Per-call recognition memo for alias visits, created on the first; first visits reuse the
  // capture's recognition.
  let kinds: Map<object, symbol> | undefined
  const kindOf = (object: object): symbol => {
    let kind = (kinds ??= new Map<object, symbol>()).get(object)
    if (kind === undefined) kinds.set(object, (kind = recognize(types, object)))
    return kind
  }
  const currents = alignment?.currents
  const occupants = alignment?.occupants
  const visit = (current: unknown, edge: Edge): void => {
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
    if (slots === undefined) types.policies[node.layout.kind].aligned(node, candidate, visit)
    else replayOccupants(node, slots, visit)
  }
  visit(old, { node: 0 })
  return aligned
}
