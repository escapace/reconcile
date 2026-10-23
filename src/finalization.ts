import { isObject } from './object-property'
import { ATOM_KIND } from './constants'
import { OBSERVED_ACCESSOR } from './types/object'
import { recognize } from './adapters/recognition'
import type { DraftSession } from './draft-session'
import { finalizationAccessorUnstable } from './error'
import { chooseSpecial } from './graph/provenance'
import { RequirementClosure } from './graph/requirements'
import { propertyDescriptor } from './object-property'
import { restoreIdentities, type FinalizationFacts } from './restore-identities'
import type {
  DraftState,
  FinalizedReference,
  Layout,
  MaterializationTraversal,
  PrototypeRead,
  ReuseNode,
  SpecialFacts,
  SpecialPolicy,
} from './types'
import { Detached, isDataDescriptor } from './standard-prototypes'

// The kept child list of an object without object children.
const NO_CHILDREN: readonly object[] = /* @__PURE__ */ Object.freeze([])

/** Retains observed structural slots for later activation without rereading their source. */
interface PendingActivation {
  readonly record: ReuseNode | undefined
  readonly slots: Array<{ readonly currentBacked: boolean; readonly value: unknown }> | undefined
}

/** Owns finite activation facts and dormant records for one finalization discovery pass. */
interface Discovery {
  clonesSpecialValues: boolean
  readonly closure: RequirementClosure<object>
  // Created on the first dormant record.
  dormant: Map<object, PendingActivation> | undefined
}

/** Separates probe, discovery and sealed caches so facts cannot outlive their phase. */
type ObservationPhase = {
  nativeOwners: WeakMap<object, object> | undefined
  readonly required: WeakMap<object, boolean>
  readonly values: WeakMap<object, unknown>
} & (
  { readonly kind: 'discover'; readonly plan: Discovery } | { readonly kind: 'probe' | 'sealed' }
)

// This object is owned by one finalization call, never by recipe-visible handles.
// Failed observations abandon the entire phase; there is no shared state to restore.
export class Finalization extends Detached {
  declare private accessorObservations: WeakMap<object, Map<PropertyKey, unknown>> | undefined
  // The complete object-child list of each object whose walk found no child needing a copy, in
  // slot order; created on the first. Produce.SettledChildren.
  declare private walked: Map<object, readonly object[]> | undefined
  // Native kind knowledge for one observation phase; never attached to application objects.
  declare private forcedOwnedCopies: WeakSet<object> | undefined
  // Created on the first recognition.
  declare private kinds: Map<object, symbol> | undefined
  // How many times a walk met an object its question visited but has not settled.
  declare private guards: number
  declare private phase: ObservationPhase
  // The prototype each recognition read, for identity restoration's storage check; it lives
  // as long as `kinds` (Types.Ingress).
  declare private prototypes: Map<object, object | null> | undefined
  declare private readonly read: PrototypeRead
  declare readonly session: DraftSession
  // The current question's pending negative answers; created on the first.
  declare private unsettled: object[] | undefined
  // Created at the first forced special copy; until then no value needs one.
  declare private untrackedSpecialsToClone: WeakSet<object> | undefined

  constructor(session: DraftSession) {
    super()
    this.session = session
    this.accessorObservations = undefined
    this.walked = undefined
    this.kinds = undefined
    this.guards = 0
    this.unsettled = undefined
    this.prototypes = undefined
    this.read = { known: false, prototype: null }
    this.phase = {
      kind: 'probe',
      nativeOwners: undefined,
      required: new WeakMap(),
      values: new WeakMap(),
    }
    this.untrackedSpecialsToClone = undefined
    this.forcedOwnedCopies = undefined
  }

  private get materializationPlan(): Discovery | undefined {
    return this.phase.kind === 'discover' ? this.phase.plan : undefined
  }

  /** Recognizes once per unknown-identity certificate lifetime; accessor effects end it. */
  kindOf(value: object): symbol {
    let kind = this.kinds?.get(value)
    if (kind === undefined) {
      // A drafted object's kind was established when its state was created.
      kind = this.session.statesByIdentity.get(value)?.kind
      if (kind === undefined) {
        const read = this.read
        read.known = false
        kind = recognize(this.session.types, value, read)
        if (read.known) (this.prototypes ??= new Map()).set(value, read.prototype)
      }
      ;(this.kinds ??= new Map()).set(value, kind)
    }
    return kind
  }

  /**
   * Finalizes one recipe result through isolated observation and immutable selection.
   *
   * @remarks
   * Discovery captures every structural subtree and its slot provenance. Late copy requirements
   * activate stored slots without observing the container again. Special copies or accessor
   * observations require a sealed projection, which incorporates receiver writes and rejects
   * newly encountered accessors before immutable selection publishes the graph.
   */
  run(value: object): unknown {
    // Preserve the pre-materialization getter discovery boundary.
    this.needsMaterialization(value)
    const plan: Discovery = {
      clonesSpecialValues: false,
      closure: new RequirementClosure<object>(),
      dormant: undefined,
    }
    // The probe settled every negative reachability answer before any discovery work, and no
    // native write happens between the two passes, so discovery reuses those answers instead
    // of reading the unchanged subtrees again. The probe materializes nothing, so its value
    // memo is still empty and discovery starts from it.
    const discovery: ObservationPhase = {
      kind: 'discover',
      nativeOwners: undefined,
      plan,
      required: this.phase.required,
      values: this.phase.values,
    }
    this.phase = discovery
    const result = this.materializeContainerSlot(value, false)
    if (plan.dormant !== undefined)
      for (const node of plan.closure.facts) {
        const activation = plan.dormant.get(node)
        if (activation === undefined) continue
        plan.dormant.delete(node)
        const slots = activation.slots!
        for (let index = 0; index < slots.length; index += 1)
          activation.record!.children[index] = this.materializeContainerSlot(
            slots[index].value,
            slots[index].currentBacked,
          )
      }
    // The sealed phase is entered only when something materializes in it: a projection, or the
    // fallback below. Nothing reads the phase in between.
    const sealed = (): unknown => {
      if (this.phase.kind !== 'sealed')
        this.phase = {
          kind: 'sealed',
          nativeOwners: undefined,
          required: new WeakMap(),
          values: new WeakMap(),
        }
      return this.materializeContainerSlot(value, false)
    }
    const project = plan.clonesSpecialValues || this.accessorObservations !== undefined
    const finalized = project ? sealed() : result
    if (!isObject(finalized)) return finalized
    const { types } = this.session
    const kindOf = (value: object): symbol => this.kindOf(value)
    // Discovery kept unchanged subtrees as fixed leaves. When the kernel cannot keep every
    // settled record, the sealed pass (already current) materializes everything and selects again.
    return (
      restoreIdentities(types, finalized as FinalizedReference, project, kindOf, this.facts()) ??
      restoreIdentities(types, sealed() as FinalizedReference, true, kindOf, this.facts())!
    )
  }

  /** What this finalization read that identity restoration would otherwise read again. */
  private facts(): FinalizationFacts {
    return { prototypes: this.prototypes, walked: this.walked }
  }

  /**
   * Determines whether reachable draft changes or special values require rebuilding a value.
   *
   * @remarks
   * Records parent dependencies during planning. A negative result is cached as soon as its
   * search ends, unless the search met an object this question visited but has not settled, which
   * only a cycle back into the walk produces; such a pending result is cached only once the whole
   * question settles negative (Produce.SettledChildren).
   */
  needsMaterialization(
    value: unknown,
    knownKind: symbol | undefined = undefined,
    traversal?: MaterializationTraversal,
  ): boolean {
    const plan = this.materializationPlan
    if (plan !== undefined && traversal !== undefined && isObject(value)) {
      const child = this.session.statesByIdentity.get(value)?.base ?? value
      plan.closure.imply(child, traversal.parent)
    }
    if (traversal !== undefined)
      return this.checkMaterialization(value, knownKind, traversal.visited)
    // A handle needs unwrapping whatever its base holds, which is checkMaterialization's first
    // answer; it needs no visited set.
    const state = isObject(value) ? this.session.statesByIdentity.get(value) : undefined
    if (state !== undefined && state.base !== value) return true
    const visited = new Set<object>()
    const outer = this.unsettled
    this.unsettled = undefined
    const result = this.checkMaterialization(value, knownKind, visited)
    // The check may have created the list, which narrowing cannot see.
    const unsettled = this.unsettled as object[] | undefined
    this.unsettled = outer
    // Pending answers settle once the entire reachable check does; every other visited object
    // settled when its own check ended.
    if (!result && unsettled !== undefined)
      for (const node of unsettled) this.phase.required.set(node, false)
    return result
  }

  /** Checks one reachable value; a cycle-guard hit makes the answers that lean on it pending. */
  private checkMaterialization(
    value: unknown,
    knownKind: symbol | undefined,
    visited: Set<object>,
  ): boolean {
    if (!isObject(value)) {
      return false
    }

    // A handle needs unwrapping even when its base is unchanged. Do not cache
    // this answer against the base: materializeState can still reuse that base.
    const state = this.session.statesByIdentity.get(value)
    const base = state?.base ?? value
    if (base !== value) return true
    const memo = this.phase.required
    if (this.materializationPlan?.closure.holds(base) === true) {
      return true
    }
    const cached = memo.get(base)

    if (cached !== undefined) {
      return cached
    }

    if (this.changedBefore(value, state)) {
      memo.set(base, true)
      return true
    }

    if (visited.has(base)) {
      // Visited and unsettled: still being walked, or pending.
      this.guards += 1
      return false
    }

    visited.add(base)
    // A negative answer is pending exactly when its walk met such an object.
    const guards = this.guards
    // Descendant accessor reads can draft this base and write through it; look its state up again.
    const result =
      this.checkDescendantsForMaterialization(base, state?.kind ?? knownKind, visited) ||
      this.session.statesByIdentity.get(base)?.modified === true ||
      this.accessorObservations?.has(base) === true

    if (result) memo.set(base, true)
    // A negative answer that leaned on no pending object is final at once.
    else if (this.guards === guards) memo.set(base, false)
    else (this.unsettled ??= []).push(base)
    return result
  }

  /** Whether an object needs a copy before its children are read: written, or a special value
   * with a copy. */
  private changedBefore(value: object, state: DraftState | undefined): boolean {
    return (
      state?.modified === true ||
      this.untrackedSpecialsToClone?.has(value) === true ||
      (state === undefined &&
        (this.session.specialCloneCloneToBase?.has(value) === true ||
          this.session.specialCloneBaseToClone?.has(value) === true))
    )
  }

  /** Checks type-declared copy dependencies in their native observation order. */
  private stableSpecialDependencies(value: object, policy: SpecialPolicy): boolean {
    return policy.dependencies(value, (dependency, dependencyKind) => {
      if (this.untrackedSpecialsToClone?.has(dependency) === true) return false
      if (this.session.specialCloneCloneToBase?.has(dependency) === true)
        return (
          (this.materializeContainerSlot(dependency, false) as FinalizedReference).target ===
          dependency
        )
      const clone = this.session.specialCloneBaseToClone?.get(dependency)
      return (
        clone === undefined ||
        (policy.dependencyEquivalent?.(value, dependency, clone, this.session) ??
          this.session.types.specials[dependencyKind]!.equivalent(dependency, clone))
      )
    })
  }

  /** Collects the native equivalence and provenance facts for a special value's decision. */
  private specialFacts(
    value: object,
    currentBacked: boolean,
    copyBase: object | undefined,
    copy: object | undefined,
    policy: SpecialPolicy,
  ): SpecialFacts {
    const forced = this.untrackedSpecialsToClone?.has(value) === true
    const dependenciesStable =
      copyBase === undefined && !forced ? this.stableSpecialDependencies(value, policy) : true
    const equivalent =
      copyBase !== undefined
        ? this.forcedOwnedCopies?.has(value) !== true && policy.equivalent(copyBase, value)
        : copy === undefined || forced || !dependenciesStable
          ? true
          : policy.equivalent(value, copy)
    return {
      currentBacked,
      dependenciesStable,
      equivalent,
      forced,
      origin: copyBase !== undefined ? 'copy' : copy !== undefined ? 'base' : 'untracked',
    }
  }

  /** A changed native owner keeps its registered child copies through sealed replay. */
  private forceOwnedChildren(value: object, policy: SpecialPolicy): void {
    if (policy.ownsDependencies !== true) return
    policy.dependencies(value, (child) => {
      const copy =
        this.session.specialCloneBaseToClone?.get(child) ??
        (this.session.specialCloneCloneToBase?.has(child) === true ? child : undefined)
      if (copy !== undefined && this.forcedOwnedCopies?.has(copy) !== true) {
        ;(this.forcedOwnedCopies ??= new WeakSet()).add(copy)
        this.phase.values.delete(copy)
        const base = this.session.specialCloneCloneToBase?.get(copy)
        if (base !== undefined) this.phase.values.delete(base)
        const plan = this.materializationPlan
        if (plan !== undefined) plan.clonesSpecialValues = true
      }
      if (copy !== undefined) {
        const owner = this.session.nativeOwners?.get(copy)
        if (owner !== undefined) (this.phase.nativeOwners ??= new WeakMap()).set(copy, owner)
      }
      return true
    })
  }

  /** Memoizes a resolved object identity that needs no structural reuse analysis. */
  private recordLeaf(target: object, memoKey: object, leaf?: true): FinalizedReference {
    const reference = { discoveredBy: undefined, layout: undefined, leaf, target }
    this.phase.values.set(memoKey, reference)
    return reference
  }

  /** Finalizes a slot using its provenance to distinguish base-backed reuse from replacement values. */
  materializeContainerSlot(value: unknown, isCurrentBackedSlot: boolean): unknown {
    if (!isObject(value)) {
      return value
    }

    // A drafted value is memoized under its base, never under its handle, so its state is
    // found first and the memo is read once, by base.
    const draftState = this.session.statesByIdentity.get(value)

    if (draftState !== undefined) {
      return this.materializeState(draftState)
    }

    const memo = this.phase.values
    const cached = memo.get(value)

    if (cached !== undefined) {
      return cached
    }

    const copyBase = this.session.specialCloneCloneToBase?.get(value)
    const copy = this.session.specialCloneBaseToClone?.get(value)
    // Preserve the native observation boundary: authored base references resolve
    // their registered copy before classifying or observing the base again.
    if (
      copyBase === undefined &&
      copy !== undefined &&
      (!isCurrentBackedSlot || this.forcedOwnedCopies?.has(copy) === true)
    ) {
      const result = this.materializeContainerSlot(copy, false)
      memo.set(value, result)
      return result
    }
    const kind = this.kindOf(copyBase ?? value)
    // An atom is a fixed leaf kept by identity, as a function slot keeps its function.
    if (kind === ATOM_KIND) return this.recordLeaf(value, value, true)
    const policy = this.session.types.specials[kind]
    if (policy === undefined) {
      const active = this.needsMaterialization(value, kind)
      // The probe settled that nothing below an unchanged object changed, whether `current`
      // backs it or the recipe inserted it, so during discovery it is a fixed leaf kept by
      // identity, without observing, recording or selecting its subtree; as a record its check
      // could only pass, and the selector's best choices keep it (Produce.PromotedLeaves). If the
      // kernel finds no plan, or a special clone sets the projection, the sealed pass
      // materializes everything.
      if (!active && this.materializationPlan !== undefined)
        return this.recordLeaf(value, value, true)
      return this.materializeDraftableObject(
        kind,
        value,
        undefined,
        value,
        isCurrentBackedSlot ? value : undefined,
        active,
      )
    }
    return this.materializeSpecial(value, isCurrentBackedSlot, copyBase, copy, policy)
  }

  /** Applies a special value's proven provenance decision before observing copy dependencies. */
  private materializeSpecial(
    value: object,
    isCurrentBackedSlot: boolean,
    copyBase: object | undefined,
    copy: object | undefined,
    policy: SpecialPolicy,
  ): unknown {
    const memo = this.phase.values
    const decision = chooseSpecial(
      this.specialFacts(value, isCurrentBackedSlot, copyBase, copy, policy),
    )
    if (decision === 'base') return this.recordLeaf(copyBase!, value)
    if (decision === 'source') {
      if (copyBase !== undefined) this.forceOwnedChildren(value, policy)
      return this.recordLeaf(value, value)
    }
    if (decision === 'copy') {
      const result = this.materializeContainerSlot(copy!, false)
      memo.set(value, result)
      return result
    }
    this.planSpecialClone(value)
    this.forceOwnedChildren(value, policy)
    policy.dependencies(value, (dependency) => {
      this.planSpecialClone(dependency)
      return true
    })
    return this.recordLeaf(
      policy.copy(
        value,
        (child) => (this.materializeContainerSlot(child, false) as FinalizedReference).target,
        this.phase,
      ),
      value,
    )
  }

  /**
   * Captures one structural payload and its candidate base edges.
   *
   * @remarks
   * Observe shape before registering the record, then register before traversing children so
   * cycles resolve to that same record. Each kind retains its own slot and observation rules.
   */
  private materializeDraftableObject(
    kind: symbol,
    source: object,
    state: DraftState | undefined,
    memoKey: object,
    currentBackedBase?: object,
    active = true,
  ): ReuseNode {
    const base = state?.base ?? currentBackedBase
    const plan = this.materializationPlan
    // Dormant records keep their observed slots for later activation; active ones need none.
    const observer = new DraftObservation(
      this,
      this.phase.values,
      state,
      memoKey,
      base ?? source,
      base,
      active,
      plan,
      active || plan === undefined ? undefined : [],
    )
    this.session.types.structural[kind].observeDraft(source, observer)
    return observer.record!
  }

  /** Captures one draft state and records whether its slots need semantic resolution. */
  private materializeState(state: DraftState): object {
    const cached = this.phase.values.get(state.base)

    if (cached !== undefined) {
      return cached as object
    }

    const active = state.modified || this.needsMaterialization(state.base)
    // A drafted but unchanged object is backed by `current`; see materializeContainerSlot.
    if (!active && this.materializationPlan !== undefined)
      return this.recordLeaf(state.base, state.base, true)

    const source = state.source()

    const result = this.materializeDraftableObject(
      state.kind,
      source,
      state,
      state.base,
      undefined,
      active,
    )
    return result
  }

  /** Records an unmanaged special-value copy requirement before a planning cache can hide it. */
  private planSpecialClone(value: object): void {
    if (
      this.session.specialCloneBaseToClone?.has(value) === true ||
      this.session.specialCloneCloneToBase?.has(value) === true ||
      this.untrackedSpecialsToClone?.has(value) === true
    ) {
      return
    }
    this.untrackedSpecialsToClone ??= new WeakSet()
    this.untrackedSpecialsToClone.add(value)
    if (this.materializationPlan !== undefined) {
      this.materializationPlan.clonesSpecialValues = true
      this.materializationPlan.closure.require(value)
    }
  }

  /**
   * Reads a finalization slot, capturing each accessor result through an isolated receiver.
   *
   * @remarks
   * Data properties keep their ordinary read behavior. Accessor observations are keyed by base and
   * property, shared across finalization passes, and separate from recipe reads. Once observations
   * are sealed, encountering an unobserved accessor throws instead of repeating application code.
   */
  readTraversalProperty(value: object, key: PropertyKey, knownState?: DraftState): unknown {
    const properties = knownState?.properties
    const own = properties?.ownDescriptor(key)
    const descriptor =
      properties === undefined
        ? propertyDescriptor(value, key)
        : (own ?? propertyDescriptor(properties.sourcePrototype(), key))
    if (descriptor !== undefined && !isDataDescriptor(descriptor))
      return this.observeAccessor(value, key, knownState)
    if (properties === undefined) return Reflect.get(value, key) as unknown
    // An own data property's descriptor was just read; its value needs no second presence check.
    return own === undefined ? properties.read(key) : properties.ownValue(key, own)
  }

  /** Runs an accessor once per base and key through the draft receiver, then reuses its result. */
  private observeAccessor(value: object, key: PropertyKey, knownState?: DraftState): unknown {
    const receiver = knownState?.handle ?? this.session.materializeChild(value)
    // A Vue proxy of a draft, such as `reactive(draft)`, stands for that draft.
    const state = knownState ?? this.session.statesByIdentity.get(receiver)!
    this.accessorObservations ??= new WeakMap()
    let observations = this.accessorObservations.get(state.base)
    if (observations === undefined) {
      observations = new Map()
      this.accessorObservations.set(state.base, observations)
    }
    if (observations.has(key)) return observations.get(key)
    if (this.phase.kind === 'sealed') throw finalizationAccessorUnstable(key)
    // A getter read through a Vue proxy returns a draft wrapped in a Vue proxy; it stands for the
    // draft, as a recipe read gives it.
    let observed = state.properties!.read(key, receiver)
    if (isObject(observed)) observed = this.session.wrappedDraft(observed) ?? observed
    this.kinds = undefined
    this.prototypes = undefined
    observations.set(key, observed)
    if (this.materializationPlan !== undefined) this.materializationPlan.closure.require(state.base)
    return observed
  }

  /**
   * Visits the kind-specific edge surface until a descendant requires materialization. A walk
   * that visits every child keeps their objects, so identity restoration need not read them again
   * (Produce.SettledChildren); one that stops early keeps nothing.
   */
  private checkDescendantsForMaterialization(
    value: object,
    knownKind: symbol | undefined,
    visited: Set<object>,
  ): boolean {
    let children: object[] | undefined
    const found = this.session.types.policies[knownKind ?? this.kindOf(value)].someChild(
      value,
      (source, key) => this.readTraversalProperty(source, key),
      (child) => {
        // A primitive needs nothing and implies nothing (checkMaterialization's first answer).
        if (!isObject(child)) return false
        ;(children ??= []).push(child)
        return this.needsMaterialization(child, undefined, { parent: value, visited })
      },
    )
    if (!found) (this.walked ??= new Map()).set(value, children ?? NO_CHILDREN)
    return found
  }
}

/**
 * Receives one structural observation for finalization.
 *
 * @remarks
 * One private object per observed record replaces per-record callbacks; it holds only the
 * record under construction and is never reachable from application code.
 */
class DraftObservation extends Detached implements PendingActivation {
  declare readonly active: boolean
  declare readonly base: object | undefined
  declare readonly finalization: Finalization
  declare readonly memoKey: object
  declare readonly plan: Discovery | undefined
  declare readonly properties: DraftState['properties']
  declare record: ReuseNode | undefined
  declare readonly slots: PendingActivation['slots']
  declare readonly state: DraftState | undefined
  declare readonly target: object
  // The memo of the phase that created this observer; a phase never changes during an
  // observation, and a dormant activation reads only `record` and `slots`.
  declare readonly values: WeakMap<object, unknown>

  constructor(
    finalization: Finalization,
    values: WeakMap<object, unknown>,
    state: DraftState | undefined,
    memoKey: object,
    target: object,
    base: object | undefined,
    active: boolean,
    plan: Discovery | undefined,
    slots: PendingActivation['slots'] | undefined,
  ) {
    super()
    this.active = active
    this.base = base
    this.finalization = finalization
    this.memoKey = memoKey
    this.plan = plan
    this.properties = state?.properties
    this.record = undefined
    this.slots = slots
    this.state = state
    this.target = target
    this.values = values
  }

  begin(layout: Layout): void {
    const record: ReuseNode = {
      attributes: undefined,
      children: [],
      collectedAs: undefined,
      collectedBy: undefined,
      discoveredBy: undefined,
      keys: undefined,
      layout,
      leaf: undefined,
      observed: undefined,
      settled: !this.active,
      target: this.target,
    }
    this.record = record
    this.values.set(this.memoKey, record)
    const plan = this.plan
    if (plan !== undefined) {
      if (this.slots === undefined) plan.closure.require(this.memoKey)
      else (plan.dormant ??= new Map()).set(this.memoKey, this)
    }
  }

  edge(value: unknown, key?: PropertyKey, backed?: boolean, attributes?: number): void {
    const finalization = this.finalization
    const record = this.record!
    const currentBacked = backed === true
    if (key !== undefined) (record.keys ??= []).push(key)
    if (this.slots !== undefined) this.slots.push({ currentBacked, value })
    if (!isObject(value)) {
      // A primitive slot resolves to itself in every phase.
      record.children.push(value)
      if (attributes === undefined) return
      ;(record.attributes ??= []).push(attributes)
      if ((attributes & OBSERVED_ACCESSOR) !== 0)
        (record.observed ??= [])[record.children.length - 1] = value
      return
    }
    const resolve = this.active || this.resolvesInactive(value)
    record.children.push(
      resolve
        ? finalization.materializeContainerSlot(value, currentBacked)
        : { discoveredBy: undefined, layout: undefined, leaf: undefined, target: value },
    )
    if (attributes === undefined) return
    ;(record.attributes ??= []).push(attributes)
    // The raw value lets reuse keep the accessor only if it returned the resolved child itself.
    if ((attributes & OBSERVED_ACCESSOR) !== 0)
      (record.observed ??= [])[record.children.length - 1] = value
  }

  /** Records an inactive record's implication and decides whether its child is resolved. */
  resolvesInactive(value: object): boolean {
    const finalization = this.finalization
    // An active parent is already a closure fact; SeededRequirements proves that omitting
    // implications into initial facts preserves the closure.
    const plan = this.plan
    if (plan !== undefined)
      plan.closure.imply(
        finalization.session.statesByIdentity.get(value)?.base ?? value,
        this.memoKey,
      )
    // Unchanged special children of an inactive record stay settled leaves in every phase;
    // unchanged structural children become fixed leaves in materializeContainerSlot.
    if (this.values.get(value) !== undefined) return true
    const kind = finalization.kindOf(value)
    return finalization.session.types.specials[kind] === undefined
      ? true
      : finalization.needsMaterialization(value, kind)
  }

  read(value: object, key: PropertyKey): unknown {
    return this.finalization.readTraversalProperty(value, key, this.state)
  }
}
