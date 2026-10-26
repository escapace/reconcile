import { atomValue, isNode } from '../graph/edge'
import { isObject, prototypeOf } from '../object-property'
import { ownValue } from '../types/shared/properties'
import { ATOM_KIND } from '../constants'
import { atomPrototype } from '../object-property'
import { OBJECT_KIND } from '../types/object'
import { recognize, recognizeStructure } from '../adapters/recognition'
import { noValue } from '../types/shared/empty'
import { Detached } from '../standard-prototypes'
import type {
  BuildingNode,
  CapturedGraph,
  CapturedNode,
  CaptureEdge,
  Edge,
  Layout,
  NodeEdge,
  Primitive,
  PrototypeRead,
  PublicationRegistry,
} from '../types'

/** Records an atom as a value edge, kept by reference like a function. */
function atom(references: Map<object, Edge>, source: object): Edge {
  const edge = { node: undefined, value: source }
  references.set(source, edge)
  return edge
}

/**
 * One aligned capture: traverses native observations and records the graph.
 *
 * @remarks
 * Memoize the private reference before observing children. Construction edges may precede begin;
 * their child must finish before the parent's constructor consumes its response. Synchronous
 * delivery preserves accessor effects at the native module boundary.
 * `snapshot` has its own traversal with the same order. The node under observation is a field,
 * restored after each child, whose observation nests inside one of its parent's edges, so one
 * pair of callbacks serves every node.
 */
class AlignedCapture extends Detached {
  declare private readonly beginCallback: (layout: Layout) => void
  // The prototype `classify` read for a plain-object kind, handed to that object's observer.
  declare private classified: object | null | undefined
  // Every object inside a kept subtree, marked by the walk that kept it; created on the first
  // walk, and unmarked again when a walk reaches a root.
  declare closure: Set<object> | undefined
  declare currents: Array<object | undefined>
  declare private readonly edgeCallback: CaptureEdge
  // The kind recognized for each aligned object found to be of another kind than its node's;
  // created on the first, so discovery does not recognize it again.
  declare kinds: Map<object, symbol> | undefined
  declare nodes: Array<BuildingNode | CapturedNode>
  declare occupants: Array<unknown[] | undefined>
  // The prototype capture read of each node's aligned current object; undefined when unread.
  declare prototypes: Array<object | null | undefined>
  // The node first aligned with each current object: the first such object and its node in two
  // fields, the rest in a map created on the second; and for an object aligned at more than one
  // node the value read at each of its keys, so that a key is read once, created on the first
  // object aligned twice.
  declare alignedAt: Map<object, number> | undefined
  declare firstAligned: object | undefined
  declare firstAlignedAt: number
  declare reads: Map<object, Map<PropertyKey, unknown>> | undefined
  // The one prototype read shared by recognition and its caller for the object at hand.
  declare private readonly read: PrototypeRead
  // The root's prototypes, read by the caller before capture.
  declare private readonly nextPrototype: object | null | undefined
  declare private pendingPrototype: object | null | undefined
  // The walk's state; `pending` is the occupant handed from the parent's aligned read to the
  // child's reservation.
  declare private count: number
  declare private currentReference: NodeEdge | undefined
  declare private currentSource: object | undefined
  declare private readonly nextRoot: unknown
  declare private pending: object | undefined
  declare private readonly references: Map<object, Edge>
  declare private readonly root: object | undefined
  declare sources: object[]
  declare private readonly types: PublicationRegistry

  constructor(
    types: PublicationRegistry,
    value: unknown,
    current: object | undefined,
    valuePrototype: object | null | undefined,
    currentPrototype: object | null | undefined,
  ) {
    super()
    this.classified = undefined
    this.closure = undefined
    this.currents = []
    this.kinds = undefined
    this.nodes = []
    this.occupants = []
    this.prototypes = []
    this.alignedAt = undefined
    this.firstAligned = undefined
    this.firstAlignedAt = 0
    this.reads = undefined
    this.read = { known: false, prototype: null }
    this.nextPrototype = valuePrototype
    this.pendingPrototype = currentPrototype
    // One begin/edge pair per capture serves every node: the observed node is a field.
    const begin = (layout: Layout): void => {
      this.begin(layout)
    }
    const edge: CaptureEdge = (child, key, knownKind, construction) =>
      this.edge(child, key, knownKind, construction)
    this.beginCallback = begin
    this.edgeCallback = edge
    this.pending = current
    this.currentReference = undefined
    this.references = new Map()
    this.root = current
    this.count = 0
    this.currentSource = undefined
    this.sources = []
    this.types = types
    this.nextRoot = value
  }

  // The plain-object fallback reads the prototype once: an atom becomes a value edge, kept by
  // reference like a function, and an object's observer receives the prototype read here.
  visit(source: unknown, kind?: symbol): Edge {
    if (!isObject(source)) return source as Primitive
    const known = this.references.get(source)
    if (known !== undefined) return known
    // The root's prototype was read before capture; any other object's is read once here.
    const read = this.share(source === this.nextRoot ? this.nextPrototype : undefined)
    const structural = kind ?? recognizeStructure(this.types, source, read)
    if (structural !== OBJECT_KIND) return this.observe(source, structural)
    const prototype = prototypeOf(source, read)
    // reconcile already found that the next root is no atom.
    return source !== this.nextRoot &&
      prototype !== Object.prototype &&
      prototype !== null &&
      atomPrototype(prototype)
      ? atom(this.references, source)
      : this.observe(source, structural, prototype)
  }

  private observe(source: object, kind: symbol, prototype?: object | null): Edge {
    const reference = this.reserve(this.count++)
    this.references.set(source, reference)
    const policy = this.types.policies[kind]
    const outerSource = this.currentSource
    const outerReference = this.currentReference
    this.currentSource = source
    this.currentReference = reference
    policy.observe(source, this.beginCallback, this.edgeCallback, 'publication', prototype)
    this.currentSource = outerSource
    this.currentReference = outerReference
    // Native policies supply begin before returning; all graph nodes are sealed.
    this.nodes[reference.node] = policy.seal(this.nodes[reference.node] as CapturedNode)
    return reference
  }

  private reserve(index: number): NodeEdge {
    const node: BuildingNode = {
      attributes: undefined,
      edges: [],
      keys: [],
      layout: undefined,
      observed: undefined,
      pinned: undefined,
    }
    const aligned = this.pending
    // The first node's tables are exact literals; a later node grows them.
    if (index === 0) {
      this.nodes = [node]
      this.currents = [aligned]
      this.prototypes = [this.pendingPrototype]
      this.occupants = [undefined]
    } else {
      this.nodes[index] = node
      this.currents[index] = aligned
      this.prototypes[index] = this.pendingPrototype
      this.occupants[index] = undefined
    }
    if (aligned !== undefined) this.alignAt(aligned, index)
    this.pending = undefined
    this.pendingPrototype = undefined
    return { node: index }
  }

  // Records the node aligned with `object`; an object aligned a second time gets the table of
  // its reads so far, which every later read of it goes through.
  private alignAt(object: object, index: number): void {
    let alignedAt = this.alignedAt
    if (alignedAt === undefined) {
      const first = this.firstAligned
      if (first === undefined) {
        this.firstAligned = object
        this.firstAlignedAt = index
        return
      }
      alignedAt = this.alignedAt = new Map<object, number>([[first, this.firstAlignedAt]])
    }
    const first = alignedAt.get(object)
    if (first === undefined) alignedAt.set(object, index)
    else if (this.reads?.has(object) !== true)
      (this.reads ??= new Map()).set(
        object,
        tableOf((this.nodes[first] as BuildingNode).keys, this.occupants[first]),
      )
  }

  // The occupant of `aligned` at `key`: the value read for another node, else one read now.
  private occupantOf(aligned: object, key: PropertyKey): unknown {
    const table = this.reads?.get(aligned)
    if (table?.has(key) === true) return table.get(key)
    const value = ownValue(aligned, key)
    table?.set(key, value)
    return value
  }

  // The driver calls begin/edge only while this node is under construction.
  private begin(layout: Layout): void {
    const index = this.currentReference!.node
    ;(this.nodes[index] as BuildingNode).layout = layout
    if (index === 0 && this.sources.length === 0) this.sources = [this.currentSource!]
    else this.sources[index] = this.currentSource!
    const aligned = this.currents[index]
    if (aligned === undefined) return
    const read = this.share(this.prototypes[index])
    // reconcile already found that the current root is no atom.
    const kind =
      index === 0
        ? recognizeStructure(this.types, aligned, read)
        : recognize(this.types, aligned, read)
    if (kind === layout.kind) this.prototypes[index] = read.known ? read.prototype : undefined
    else {
      this.currents[index] = undefined
      ;(this.kinds ??= new Map()).set(aligned, kind)
    }
  }

  // Resets the shared prototype read for a new object, holding `prototype` when already known.
  private share(prototype: object | null | undefined): PrototypeRead {
    const read = this.read
    read.known = prototype !== undefined
    read.prototype = prototype ?? null
    return read
  }

  private edge(
    value: unknown,
    key: PropertyKey | undefined,
    knownKind: symbol | undefined,
    construction: boolean | undefined,
  ): unknown {
    const reference = this.currentReference!
    const node = this.nodes[reference.node] as BuildingNode
    // The key precedes its edge while the child is captured, so that the table of a shared
    // object's reads, built then, names the occupant read for it.
    if (key !== undefined) node.keys.push(key)
    const child = this.adopt(reference.node, value, key, construction, knownKind)
    node.edges.push(child)
    if (construction !== true) return undefined
    // A construction child, a buffer or a URL's parameters, is a leaf whose node began already.
    if (!isNode(child)) return atomValue(child)
    const layout = this.nodes[child.node].layout!
    return this.types.policies[layout.kind].construction(layout)
  }

  // A new child is classified as `visit` classifies it.
  private classify(child: object, kind: symbol | undefined): symbol {
    const read = this.share(undefined)
    const structural = kind ?? recognizeStructure(this.types, child, read)
    this.classified = undefined
    if (structural !== OBJECT_KIND) return structural
    this.classified = prototypeOf(child, read)
    return this.classified !== Object.prototype &&
      this.classified !== null &&
      atomPrototype(this.classified)
      ? ATOM_KIND
      : structural
  }

  // The occupant of each own-property edge of an aligned object is read once here and serves
  // every later phase; an own-property edge may keep the occupant as an atom; construction edges
  // read none. The reference lookup happens once here, not again inside the visit.
  private adopt(
    parent: number,
    child: unknown,
    key: PropertyKey | undefined,
    construction: boolean | undefined,
    kind: symbol | undefined,
  ): Edge {
    const aligned = this.currents[parent]
    if (aligned === undefined || key === undefined || construction === true)
      return this.visit(child, kind)
    const occupant = this.occupantOf(aligned, key)
    this.recordOccupant(parent, occupant)
    if (!isObject(child)) return child as Primitive
    const references = this.references
    const known = references.get(child)
    const childKind = known === undefined ? this.classify(child, kind) : kind
    if (childKind === ATOM_KIND) return atom(references, child)
    const prototype = known === undefined ? this.classified : undefined
    if (
      known === undefined &&
      (Object.is(occupant, child) || this.closure?.has(child) === true) &&
      this.keep(child, childKind!)
    )
      return atom(references, child)
    if (known !== undefined) return known
    this.pending = isObject(occupant) ? occupant : undefined
    return this.observe(child, childKind!, prototype)
  }

  // Records the occupant read for the parent's next edge. A node's own-property edges all read
  // one, in edge order, and no kind mixes them with construction edges, so the list is complete.
  private recordOccupant(parent: number, occupant: unknown): void {
    ;(this.occupants[parent] ??= []).push(occupant)
  }

  // A keepable kind needs no construction input and has independent bindings. Its subtree is
  // read once before it is kept; one that contains either root is captured instead, as full
  // capture requires, and everything the walk met is protected from reuse elsewhere. The walk
  // is an explicit stack over the publication observation surface: no records, no selection.
  // It stops at the first root it meets and forgets what it marked on the way.
  // Returns whether the candidate is kept.
  private keep(candidate: object, kind: symbol): boolean {
    const types = this.types
    let policy = types.policies[kind]
    if (policy.bindings.tag !== 'independent' || policy.construction !== noValue) return false
    const closure = (this.closure ??= new Set())
    if (closure.has(candidate)) return true
    const visited: object[] = []
    const stack: object[] = []
    let source: object | undefined = candidate
    let prototype: object | null | undefined
    const edge = (child: unknown) => {
      if (isObject(child)) stack.push(child)
    }
    const push = (child: unknown): boolean => {
      edge(child)
      return false
    }
    // Atoms are leaves: the walk passes them by, classifying as `visit` does.
    const pop = (): object | undefined => {
      for (let next = stack.pop(); next !== undefined; next = stack.pop()) {
        const read = this.share(undefined)
        const nextKind = recognizeStructure(types, next, read)
        prototype = undefined
        if (nextKind === OBJECT_KIND) {
          prototype = prototypeOf(next, read)
          if (prototype !== Object.prototype && prototype !== null && atomPrototype(prototype))
            continue
        }
        policy = types.policies[nextKind]
        return next
      }
      return undefined
    }
    while (source !== undefined) {
      if (!closure.has(source)) {
        // A subtree that reaches a root is captured.
        if (source === this.nextRoot || source === this.root) {
          visited.forEach((marked) => closure.delete(marked))
          return false
        }
        closure.add(source)
        visited.push(source)
        // A kind that `someChild` lists needs no observation, which would copy its value.
        if (policy.someChild === undefined)
          policy.observe(source, noValue, edge, 'publication', prototype)
        else policy.someChild(source, ownValue, push)
      }
      source = pop()
    }
    return true
  }
}

/** The values read at `keys`, by key, from the positional `reads`. */
export function tableOf(
  keys: readonly PropertyKey[],
  reads: readonly unknown[] | undefined,
): Map<PropertyKey, unknown> {
  const table = new Map<PropertyKey, unknown>()
  if (reads === undefined) return table
  for (let index = 0; index < keys.length && index < reads.length; index += 1)
    table.set(keys[index], reads[index])
  return table
}

/**
 * Captures `value`, aligned with `current` when supplied.
 *
 * @remarks
 * Aligned capture reads, for each own-property edge of a node whose aligned current object
 * has the same kind, the occupant of that slot right after the next value, once; the read
 * serves discovery, the preflight and the first publication. A child that is the occupant
 * itself is walked once and kept as an atom edge holding the object when its kind needs no
 * construction input and has independent bindings and the walk meets neither root. Everything
 * the walk met is protected: no other position may retain it, and a later child found inside it
 * is kept the same way or, once captured, pinned to itself.
 */
export function capture(
  types: PublicationRegistry,
  value: unknown,
  current?: object,
  valuePrototype?: object | null,
  currentPrototype?: object | null,
): CapturedGraph {
  const run = new AlignedCapture(types, value, current, valuePrototype, currentPrototype)
  const root = run.visit(value)
  return {
    alignedAt: run.alignedAt,
    candidateReads: undefined,
    currents: run.currents,
    firstAligned: run.firstAligned,
    firstAlignedAt: run.firstAlignedAt,
    kinds: run.kinds,
    nodes: run.nodes as CapturedNode[],
    occupants: run.occupants,
    pinned: run.closure,
    prototypes: run.prototypes,
    reads: run.reads,
    root,
    sources: run.sources,
  }
}
