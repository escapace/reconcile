import { atomValue, isNode } from '../graph/edge'
import { hasOwn, isObject, prototypeOf } from '../object-property'
import { ATOM_KIND } from '../constants'
import { atomPrototype } from '../object-property'
import { OBJECT_KIND } from '../types/object'
import { recognize, recognizeStructure } from '../adapters/recognition'
import { storageIdentity } from '../adapters/vue'
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
 * delivery preserves iterator cleanup and accessor effects at the native module boundary.
 * `snapshot` has its own traversal with the same order. The node under observation is a field,
 * restored after each child, whose observation nests inside one of its parent's edges, so one
 * pair of callbacks serves every node.
 */
class AlignedCapture extends Detached {
  // Storage of every object a kept subtree's walk met; created on the first kept subtree.
  declare protectedStorage: Set<unknown> | undefined
  // The prototype `classify` read for a plain-object kind, handed to that object's observer.
  declare private classified: object | null | undefined
  // Objects marked by kept-subtree walks; created on the first walk.
  declare private readonly beginCallback: (layout: Layout) => void
  declare private closure: Set<object> | undefined
  declare currents: Array<object | undefined>
  declare private readonly edgeCallback: CaptureEdge
  declare nodes: Array<BuildingNode | CapturedNode>
  declare occupants: Array<unknown[] | undefined>
  // The prototype capture read of each node's aligned current object; undefined when unread.
  declare prototypes: Array<object | null | undefined>
  // The one prototype read shared by recognition and its caller for the object at hand.
  declare private readonly read: PrototypeRead
  // The root's prototypes, read by the caller before capture.
  declare private readonly nextPrototype: object | null | undefined
  declare private pendingPrototype: object | null | undefined
  // Occupant handed from the parent's aligned read to the child's reservation.
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
    this.nodes = []
    this.occupants = []
    this.prototypes = []
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
    this.protectedStorage = undefined
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
    return prototype !== Object.prototype && prototype !== null && atomPrototype(prototype)
      ? atom(this.references, source)
      : this.observe(source, structural, prototype)
  }

  private observe(source: object, kind: symbol, prototype?: object | null): NodeEdge {
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
    // The first node's tables are exact literals; a later node grows them.
    if (index === 0) {
      this.nodes = [node]
      this.currents = [this.pending]
      this.prototypes = [this.pendingPrototype]
      this.occupants = [undefined]
    } else {
      this.nodes[index] = node
      this.currents[index] = this.pending
      this.prototypes[index] = this.pendingPrototype
      this.occupants[index] = undefined
    }
    this.pending = undefined
    this.pendingPrototype = undefined
    return { node: index }
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
    if (recognize(this.types, aligned, read) === layout.kind)
      this.prototypes[index] = read.known ? read.prototype : undefined
    else this.currents[index] = undefined
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
    const child = this.adopt(reference.node, value, key, construction, knownKind)
    const node = this.nodes[reference.node] as BuildingNode
    node.edges.push(child)
    if (key !== undefined) node.keys.push(key)
    if (construction === true) {
      if (isNode(child)) {
        const layout = this.nodes[child.node]?.layout
        if (layout !== undefined) return this.types.policies[layout.kind].construction(layout)
      } else return atomValue(child)
    }
    return undefined
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

  // Own-property edges may keep the current occupant as an atom; construction edges never do.
  // The reference lookup happens once here, not again inside the visit.
  private adopt(
    parent: number,
    child: unknown,
    key: PropertyKey | undefined,
    construction: boolean | undefined,
    kind: symbol | undefined,
  ): Edge {
    const aligned = this.currents[parent]
    if (aligned === undefined || key === undefined || construction === true || !isObject(child))
      return this.visit(child, kind)
    const references = this.references
    const known = references.get(child)
    const occupant: unknown = hasOwn(aligned, key) ? Reflect.get(aligned, key) : undefined
    // An atom has no occupant entry.
    const childKind = known === undefined ? this.classify(child, kind) : kind
    if (childKind === ATOM_KIND) return atom(references, child)
    const prototype = known === undefined ? this.classified : undefined
    if (
      known === undefined &&
      (Object.is(occupant, child) || this.closure?.has(child) === true) &&
      this.keep(child, childKind!)
    ) {
      const edge = { node: undefined, value: child }
      references.set(child, edge)
      return edge
    }
    // One entry per own-property node edge, in edge order; atoms are not recorded.
    if (known === undefined || isNode(known)) (this.occupants[parent] ??= []).push(occupant)
    if (known !== undefined) return known
    this.pending = isObject(occupant) ? occupant : undefined
    return this.observe(child, childKind!, prototype)
  }

  // A keepable kind needs no construction input and has independent bindings. Its subtree is
  // read once before it is kept; one that contains either root is captured instead, as full
  // capture requires, and everything the walk met is protected from reuse elsewhere. The walk
  // is an explicit stack over the publication observation surface: no records, no selection.
  // It stops at the first root it meets and forgets what it marked on the way.
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
    const edge = (child: unknown, _key?: PropertyKey, _kind?: symbol, construction?: boolean) => {
      if (isObject(child)) stack.push(child)
      // A view's constructor receives its actual buffer; the sample it builds is dropped.
      return construction === true ? child : undefined
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
        if (source === this.nextRoot || source === this.root) {
          visited.forEach((marked) => closure.delete(marked))
          return false
        }
        closure.add(source)
        visited.push(source)
        policy.observe(source, noValue, edge, 'publication', prototype)
      }
      source = pop()
    }
    const walked = (this.protectedStorage ??= new Set())
    for (const marked of visited) walked.add(storageIdentity(marked))
    return true
  }
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
  valuePrototype?: object | null,
  currentPrototype?: object | null,
): CapturedGraph {
  const run = new AlignedCapture(types, value, current, valuePrototype, currentPrototype)
  const root = run.visit(value)
  return {
    currents: run.currents,
    nodes: run.nodes as CapturedNode[],
    occupants: run.occupants,
    protectedStorage: run.protectedStorage,
    prototypes: run.prototypes,
    root,
    sources: run.sources,
  }
}
