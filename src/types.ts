import type { PrototypeRead } from './object-property'

export type { PrototypeRead }

/**
 * The session services that draft strategies use while a recipe runs.
 *
 * @internal
 */
export interface DraftContext {
  /** Each base and each handle of a drafted object, mapped to its state. */
  readonly statesByIdentity: WeakMap<object, DraftState>
  /** Compares two values, treating a structural handle as its base. */
  isSameDraftValue: (currentValue: unknown, value: unknown) => boolean
  /** Returns the handle or special-value copy that a recipe read sees. */
  materializeChild: (value: object) => object
  /** The original of a special-value copy, such as a `Date` a recipe read; undefined otherwise. */
  copyBase: (value: object) => object | undefined
  /** The special-value copy a recipe read of `value` made, if any. */
  copyOf: (value: object) => object | undefined
  /** Draft layers of `Map` and `Set` subclasses, by subclass prototype, for this call. */
  draftLayers: Map<object, object> | undefined
}

/**
 * Tracks a structural draft's base, working copy, and recipe context.
 *
 * @remarks
 * Object and array copies hold logical descriptors; collection copies are native Map or Set
 * instances. The core reads the common state/property ports; modules own the concrete representation.
 * @internal
 */
export interface BaseDraftState {
  readonly kind: symbol
  readonly properties: PropertyDraftPort | undefined
  source: () => object
  /** Original object represented by the handle. */
  readonly base: object
  /** Recipe identity and writable-copy owner. */
  readonly context: DraftContext
  /** Working descriptor store or native collection, created when a write first requires a copy. */
  copy: object | undefined
  /** Recipe-visible identity, installed once after native handle construction. */
  handle: object | undefined
  /** Records an effective write; undo reuse is decided during finalization. */
  modified: boolean
}

/** Shared session port; concrete draft representations remain type-owned. */
export type DraftState = BaseDraftState

/**
 * Represents an object edge during immutable finalization.
 *
 * @remarks
 * Every internal object edge is a private reference, never an application object. An absent
 * layout marks a resolved leaf; structural references propose a base until reuse is settled.
 * @internal
 */
export interface FinalizedReference<L extends Layout = Layout> {
  readonly layout: L | undefined
  readonly target: object
  /** The mark of the identity compile that last discovered this reference. */
  discoveredBy: object | undefined
}

/**
 * Stores captured structural output until compatible base identities have been selected.
 *
 * @remarks
 * Children contain private references and atoms. The candidate target is immutable; selected
 * identities and fresh targets live in the shared graph kernel's binding table.
 * Native allocation metadata uses the shared captured layout representation.
 * @internal
 */
export interface ReuseNode<L extends Layout = Layout> extends FinalizedReference<L> {
  /** Stores array/object values, alternating Map keys and values, or Set members. */
  readonly children: unknown[]
  readonly layout: L
  /**
   * Captured from an inactive record: the probe settled that nothing below changed and the
   * record holds no accessor, so its payload equals its base without a second read.
   */
  readonly settled?: boolean
  /** Packs configurable, enumerable, and writable data-property flags into bits 1, 2, and 4. */
  attributes?: number[]
  /** The value each observed own accessor returned, by slot, as the getter returned it. */
  observed?: unknown[]
  /** Maps ordered array or object property names to child slots. */
  keys?: PropertyKey[]
  /** The mark of the identity compile that last collected this record, and its node there. */
  collectedAs?: NodeEdge
  collectedBy?: object
}

/** Exposes a logical descriptor store to finalization without exposing its representation. */
export interface PropertyDraftPort {
  contains: (key: PropertyKey) => boolean
  /** Returns own strings followed by symbols from the active store. */
  keys: (source: object) => PropertyKey[]
  ownDescriptor: (key: PropertyKey) => PropertyDescriptor | undefined
  /** The value of an own data property whose descriptor `ownDescriptor` just returned. */
  ownValue: (key: PropertyKey, descriptor: PropertyDescriptor) => unknown
  read: (key: PropertyKey, receiver?: unknown) => unknown
  /** Whether reads still go to the object itself, before the first write. */
  readsBase: () => boolean
  sourcePrototype: () => object | null
}

/** Receives a structural draft observation: its layout and slots, with base provenance and isolated reads. */
export interface DraftObservationContext<L extends Layout = Layout> {
  readonly base: object | undefined
  /**
   * Whether the call holds a special-value copy. Only a slot holding a value with a copy reads
   * the slot's current-backed provenance (`DraftEdge`), so without one a kind passes no
   * provenance it would have to read `base` for.
   */
  readonly edge: DraftEdge
  readonly properties: PropertyDraftPort | undefined
  readonly begin: (layout: L) => void
  readonly copies: () => boolean
  readonly read: (source: object, key: PropertyKey) => unknown
}

/** Per-call native ownership metadata, allocated only when a child is registered. */
export interface NativeOwners {
  nativeOwners: WeakMap<object, object> | undefined
}

/** Defines copy identity and dependency rules for a nonstructural value. */
export interface SpecialPolicy {
  /** Native owned dependencies cannot be rebound when this copy remains changed. */
  readonly ownsDependencies?: true
  /** Checks a copied dependency together with its native owner's serialized state. */
  readonly dependencyEquivalent?: (
    owner: object,
    source: object,
    copy: object,
    owners: NativeOwners,
  ) => boolean
  /** Copies one value; declared dependencies resolve through the caller with their known kind. */
  copy: (
    value: object,
    resolve: (dependency: object, kind: symbol) => object,
    owners: NativeOwners,
  ) => object
  equivalent: (base: object, candidate: object) => boolean
  /** Visits declared copy dependencies in native observation order, stopping on false. */
  dependencies: (value: object, visit: (value: object, kind: symbol) => boolean) => boolean
}

/**
 * Defines the complete native contract for a registered kind.
 *
 * @remarks
 * The core treats layouts as opaque and dispatches through their captured kind. Observation,
 * compatibility, publication and readback remain separate native effect boundaries; the
 * requirement scan is the preflight, repeated by the engine only after its own writes.
 * Returning true from publish reports accepted operations, not successful graph correspondence;
 * matches must subsequently verify the selected image, unless the first publication wrote nothing
 * to any node and every node reported `note.unchanged`. Copy and structural immutable facets are
 * disjoint. Implementations supply closed node references and stable, usable native observations;
 * the finite Lean proofs do not establish these JavaScript premises.
 */
export interface NativePolicy<L extends { readonly kind: symbol } = Layout> {
  /** Visits the current object's slots aligned with the node's edges, reading each own value
   * once, through `read` when given. */
  readonly aligned: (
    node: CapturedNode<L>,
    current: object | undefined,
    visit: Align,
    read?: SlotRead,
  ) => void
  /** The preflight: undefined when `current` cannot hold the node's contents, else the objects
   * its fixed slots require other nodes to keep; a policy may leave in `note` the facts it read,
   * for the first publication. */
  readonly requirements: (
    node: CapturedNode<L>,
    current: object,
    note?: PublicationNote,
  ) => readonly BoundEdge[] | undefined

  /** Supplies captured storage needed by a construction edge, when this kind provides it. */
  readonly construction: (layout: L) => object | undefined
  /** Visits direct children in native order, stopping at the first true predicate. */
  readonly someChild: (
    source: object,
    read: (source: object, key: PropertyKey) => unknown,
    test: (value: unknown) => boolean,
  ) => boolean
  /** Emits synchronously in native read order, propagating consumer failures and construction responses. */
  readonly observe: (
    value: object,
    begin: Begin<L>,
    edge: CaptureEdge,
    prototype?: object | null,
  ) => void
  /** Finalizes derived layout indexes and native collection normalization after observation. */
  readonly seal: (node: CapturedNode<L>) => CapturedNode<L>

  readonly immutable:
    | { readonly operations: SpecialPolicy; readonly tag: 'copy' }
    | {
        readonly tag: 'structural'
        /** Observes structural slots synchronously, retaining draft provenance and isolated reads. */
        readonly observeDraft: (source: object, observer: DraftObservationContext<L>) => void
        readonly reuse: (node: CapturedNode<L>, current: object, visit: Compare) => boolean
        /** Allocates the empty copy of a node; produce fills it once every copy exists. */
        readonly allocate: (node: CapturedNode<L>) => object
        /** Writes the node's slots into its copy; false when the copy cannot hold them, as when
         * two keys of a `Map` resolve to one object. */
        readonly fill: (node: CapturedNode<L>, target: object, resolve: Resolve) => boolean
      }

  readonly bindings:
    | {
        readonly tag: 'dependent'
        /** Pure sealed node IDs required before allocating a fresh target. */
        readonly dependencies: (node: CapturedNode<L>) => readonly number[]
        /** A new object of this kind creates the children its dependencies name, so such a child
         * keeps a current object only together with the owner that `requirements` names for it:
         * a URL and its `searchParams`. */
        readonly owns?: true
      }
    | { readonly tag: 'independent' }
  /**
   * Allocates privately after dependencies exist; undefined rejects this preparation before writes.
   * The per-attempt owner map links fresh native children to their attachable owner shells.
   */
  readonly allocate: (
    node: CapturedNode<L>,
    resolve: Resolve,
    owners: NativeOwners,
  ) => object | undefined
  /** Whether `current` holds the node's contents. */
  readonly matches: (node: CapturedNode<L>, current: object, visit: Compare) => boolean
  /**
   * Writes the node's contents; a policy may use the preflight facts in `note` and set
   * `note.unchanged` when it wrote nothing and its readback would accept.
   */
  readonly publish: (
    node: CapturedNode<L>,
    current: object,
    resolve: Resolve,
    owner?: (child: object, ownerKind: symbol) => object | undefined,
    note?: PublicationNote,
  ) => boolean
  /** The copy of the value whose capture made `layout`; it has no children of its own. */
  readonly snapshot: (layout: L) => object
}

/** The key list and own descriptors one property preflight read of `current`, in key order. */
export interface PreflightFacts {
  readonly descriptors: ReadonlyArray<PropertyDescriptor | undefined>
  readonly keys: readonly PropertyKey[]
}

/**
 * One per-call channel between the publication engine and a policy: the preflight leaves its
 * facts, the first publication of an ordinary target reads them, and a publication reports
 * whether it wrote nothing that its readback would reject (Property.WriteFreeReadback).
 */
export interface PublicationNote {
  facts: PreflightFacts | undefined
  /** The prototype of the object being preflighted, when capture read it; undefined otherwise. */
  prototype: object | null | undefined
  unchanged: boolean
  /** What the call already read of the object being preflighted or published, by edge position:
   * before the first write, the occupants that aligned capture or discovery read; in a later
   * pass, what the previous pass read back of the object at this node; undefined otherwise. */
  reads: readonly unknown[] | undefined
}

/** Native facets retained by each public operation. */
export type CapturePolicy<L extends Layout = Layout> = Pick<
  NativePolicy<L>,
  'construction' | 'observe'
>
export type ConstructionPolicy<L extends Layout = Layout> = Pick<
  NativePolicy<L>,
  'allocate' | 'bindings'
>
export type ImmutablePolicy<L extends Layout = Layout> = Pick<
  NativePolicy<L>,
  'immutable' | 'someChild'
>
/** A kind whose capture copies its value also lists its children (`someChild`), so the walk of a
 * subtree that stays in place, which needs only the children, copies nothing. */
export type PublicationPolicy<L extends Layout = Layout> = CapturePolicy<L> &
  ConstructionPolicy<L> &
  Partial<Pick<NativePolicy<L>, 'someChild'>> &
  Pick<NativePolicy<L>, 'aligned' | 'matches' | 'publish' | 'requirements' | 'seal'>
export type SnapshotPolicy<L extends Layout = Layout> = CapturePolicy<L> &
  Pick<NativePolicy<L>, 'snapshot'>

/**
 * The kind-indexed native dispatch of `produce`.
 *
 * @remarks
 * Payload and draft-state types are erased in the tables. Callers dispatch only with kinds
 * established by recognition or a facet's valid phase-local certificate; the tables hold the
 * built-in kinds, not every possible symbol.
 */
export type ImmutableRegistry = {
  readonly drafts: Readonly<Record<symbol, DraftStrategy>>
  readonly specials: Readonly<Record<symbol, SpecialPolicy | undefined>>
  readonly structural: Readonly<
    Record<symbol, Extract<NativePolicy['immutable'], { tag: 'structural' }>>
  >
} & NativeRegistry<ImmutablePolicy>
export type NativeRegistry<P> = {
  readonly policies: Readonly<Record<symbol, P>>
} & RecognitionRegistry
export type PublicationRegistry = NativeRegistry<PublicationPolicy>
export interface RecognitionRegistry {
  /** Reobserves the recognition prefix through a built-in kind. */
  readonly matches: (kind: symbol, value: object) => boolean
  /**
   * Returns the first matching kind in recognition order. It takes the prototype from `read` when
   * it is known and reports there the one it read.
   */
  readonly recognize: (value: object, read?: PrototypeRead) => symbol
}
export type SnapshotRegistry = Pick<NativeRegistry<SnapshotPolicy>, 'policies' | 'recognize'>

/** Recipe representation selected by the type module before the session allocates state. */
export type DraftStrategy<S extends DraftState = DraftState> =
  | {
      readonly links:
        | {
            readonly tag: 'dependent'
            readonly register: (
              source: object,
              target: object,
              visit: (copy: object, base: object) => void,
            ) => void
            readonly writable: (value: object, hasCopy: (value: object) => boolean) => boolean
          }
        | { readonly tag: 'independent' }
      readonly tag: 'copy'
    }
  | {
      readonly tag: 'structural'
      /** `prototype` is the base's prototype when ingress read it, else undefined. */
      readonly handle: (state: S, prototype?: object | null) => object
      readonly state: (base: object, context: DraftContext) => S
    }

/** Represents an opaque atom or a canonical reference into the captured node domain. A
 * primitive is its own atom edge; an object atom is wrapped. */
export type Edge<R extends { readonly node: number } = { readonly node: number }> =
  | Atom
  | Primitive
  | R

/** A value that is not an object, held as its own edge. */
export type Primitive = bigint | boolean | number | string | symbol | null | undefined

/** An object atom edge. `node` is present and undefined, so telling the two kinds apart never
 * reads a property through `Object.prototype`. */
export interface Atom {
  readonly node: undefined
  readonly value: unknown
}

/** Payload fields belong to the selected module; the core only reads its ID. */
export interface Layout {
  readonly kind: symbol
}

/**
 * Stores ordered edges and opaque native layout facts for a captured node.
 *
 * @remarks
 * A pinned node is a captured object that turned out to lie inside a kept subtree. It
 * retains its identity and is never written or read back. Objects kept at their own slot
 * never become nodes: their parent edge holds the object itself as an atom.
 */
export interface CapturedNode<L extends { readonly kind: symbol } = Layout> {
  readonly attributes: readonly number[] | undefined
  readonly edges: readonly Edge[]
  readonly keys: readonly PropertyKey[]
  readonly layout: L
  readonly observed: readonly unknown[] | undefined
  readonly pinned: object | undefined
  /** The object of `next` this node is, which capture records when it creates the node;
   * undefined in a graph that `produce` builds. */
  readonly source: object | undefined
}

/**
 * Represents a finite graph closed under all node references, including its root.
 *
 * @remarks
 * Aligned capture records, per captured node, the current object it was first aligned with, and
 * at each own-property edge the occupant it read, by edge position.
 * Candidate discovery and the first publication of the aligned object reuse those reads.
 */
export interface CapturedGraph {
  readonly nodes: readonly CapturedNode[]
  readonly root: Edge
  readonly currents?: ReadonlyArray<object | undefined>
  /** The kind capture recognized for each aligned object whose kind differs from its node's; a
   * per-call memo that discovery extends. */
  readonly kinds?: Map<object, symbol> | undefined
  readonly occupants?: ReadonlyArray<readonly unknown[] | undefined>
  /** The values discovery read at the slots of each node's other aligned objects, by object and
   * edge position; discovery creates the table on its first read. */
  candidateReads?: Array<Map<object, unknown[]> | undefined>
  /** Every object of `next` capture met, by object: a captured node's reference, or the object
   * itself as an atom edge. */
  readonly references: ReadonlyMap<object, Edge>
  /** Every object inside a pinned subtree; no other position may retain one. */
  readonly pinned?: ReadonlySet<object>
  /** The prototype capture read of each node's aligned current object; undefined when unread. */
  readonly prototypes?: ReadonlyArray<object | null | undefined>
  /** The node capture first aligned with each current object, once a second object is aligned;
   * before that, `firstAligned` and its node. */
  readonly alignedAt?: ReadonlyMap<object, number>
  readonly firstAligned?: object | undefined
  readonly firstAlignedAt?: number
  /** For each current object read at more than one node, the value read at each of its keys, so
   * that no key is read twice before the first write; created on the first such object, and
   * extended by discovery. */
  reads?: Map<object, Map<PropertyKey, unknown>> | undefined
  /** Whether an edge of an aligned object may offer another current object than the one its child
   * is aligned with: an edge without a key or with construction input, or an edge to a captured
   * node whose occupant is another object. Unset for a graph capture did not align. */
  readonly offersOther?: boolean
}

/** Installs native layout state at the observer-defined begin boundary. */
export type Begin<L extends Layout = Layout> = (layout: L) => void

/** Visits a child synchronously; construction edges return their resolved native input. */
export type CaptureEdge = (
  value: unknown,
  key?: PropertyKey,
  knownKind?: symbol,
  construction?: boolean,
) => unknown

/** Captures a child with optional current-backed provenance and property attributes. */
export type DraftEdge = (
  value: unknown,
  key?: PropertyKey,
  currentBacked?: boolean,
  attributes?: number,
) => void

/** Visits one aligned child; a property slot passes its edge's position. */
export type Align = (actual: unknown, expected: Edge, position?: number) => void

/** Reads the own value of `current` at `key`, or `undefined` when it has none. */
export type SlotRead = (current: object, key: PropertyKey) => unknown

/** Checks one observed child against the selected image of a captured edge. */
export type Compare = (actual: unknown, expected: Edge) => boolean

/** Pins a captured child node to an observed native object identity. */
export interface BoundEdge {
  readonly identity: object
  readonly node: number
}

/** A current object a node may keep, with the objects its fixed slots require other nodes to
 * keep and the facts its preflight read, when it left any. */
export interface Candidate {
  readonly facts: PreflightFacts | undefined
  readonly identity: object
  readonly required: readonly BoundEdge[]
}

/** The candidates of each node in discovery order; a pinned node's only candidate is itself. */
export type Candidates = ReadonlyArray<readonly Candidate[]>

/** Resolves an edge through the current selected image, leaving atoms unchanged. */
export type Resolve = (edge: Edge) => unknown

/** Accumulates a graph node before native sealing makes its layout consumable. */
export interface BuildingNode {
  readonly attributes: undefined
  edges: Edge[]
  keys: PropertyKey[]
  layout: Layout | undefined
  readonly observed: undefined
  readonly pinned: undefined
  readonly source: object
}

/** Supplies native equivalence and provenance facts to the finite special-value decision. */
export interface SpecialFacts {
  readonly dependenciesStable: boolean
  readonly equivalent: boolean
  readonly forced: boolean
  /** The registration relationship of the value. */
  readonly origin: 'base' | 'copy' | 'untracked'
}

/** Selects an explicit base, registered copy, fresh copy or unchanged source. */
export type SpecialDecision = 'base' | 'copy' | 'fresh' | 'source'

/** Stores a settled special identity or a structural payload eligible for fresh allocation. */
export interface ImmutableRecord {
  readonly edges: readonly Edge[]
  readonly target: object
  // Settled specials need no allocation payload or additional scalar observation.
  readonly payload: CapturedNode | undefined
}

/** Narrows an edge to a captured node reference. */
export type NodeEdge = Extract<Edge, { readonly node: number }>

/** Supplies the parent implication and provisional cycle guard for a descendant search. */
export interface MaterializationTraversal {
  readonly parent: object
  readonly visited: Set<object>
}

/** Supplies sealed immutable proposals and closed reuse failures; each record is its own storage. */
export interface ImmutableProblem {
  readonly records: readonly ImmutableRecord[]
  readonly root: number
  readonly unavailable: ReadonlySet<number>
}
