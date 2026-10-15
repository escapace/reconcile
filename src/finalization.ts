import { isObject } from './object-property'
import { recognize } from './adapters/recognition'
import type { DraftSession } from './draft-session'
import { finalizationAccessorUnstable } from './error'
import { chooseSpecial } from './graph/provenance'
import { RequirementClosure } from './graph/requirements'
import { propertyDescriptor } from './object-property'
import { restoreIdentities } from './restore-identities'
import type {
  DraftState,
  FinalizedReference,
  MaterializationTraversal,
  ReuseNode,
  SpecialFacts,
  SpecialPolicy,
} from './types'

/** Retains observed structural slots for later activation without rereading their source. */
interface PendingActivation {
  readonly record: ReuseNode
  readonly slots: Array<{ readonly currentBacked: boolean; readonly value: unknown }>
}

/** Owns finite activation facts and dormant records for one finalization discovery pass. */
interface Discovery {
  clonesSpecialValues: boolean
  readonly closure: RequirementClosure<object>
  readonly dormant: Map<object, PendingActivation>
}

/** Separates probe, discovery and sealed caches so facts cannot outlive their phase. */
type ObservationPhase = (
  { readonly kind: 'discover'; readonly plan: Discovery } | { readonly kind: 'probe' | 'sealed' }
) & {
  readonly required: WeakMap<object, boolean>
  readonly values: WeakMap<object, unknown>
  nativeOwners?: WeakMap<object, object>
}

// This object is owned by one finalization call, never by recipe-visible handles.
// Failed observations abandon the entire phase; there is no shared state to restore.
export class Finalization {
  declare private accessorObservations: WeakMap<object, Map<PropertyKey, unknown>> | undefined
  // Native kind knowledge for one observation phase; never attached to application objects.
  declare private forcedOwnedCopies: WeakSet<object> | undefined
  declare private kinds: Map<object, symbol>
  declare private phase: ObservationPhase
  declare private readonly session: DraftSession
  declare private readonly untrackedSpecialsToClone: WeakSet<object>

  constructor(session: DraftSession) {
    this.session = session
    this.accessorObservations = undefined
    this.kinds = new Map()
    this.phase = {
      kind: 'probe',
      required: new WeakMap(),
      values: new WeakMap(),
    }
    this.untrackedSpecialsToClone = new WeakSet()
    this.forcedOwnedCopies = undefined
  }

  private get materializationPlan(): Discovery | undefined {
    return this.phase.kind === 'discover' ? this.phase.plan : undefined
  }

  /** Recognizes once per unknown-identity certificate lifetime; accessor effects end it. */
  private kindOf(value: object): symbol {
    let kind = this.kinds.get(value)
    if (kind === undefined) {
      // A drafted object's kind was established when its state was created.
      kind = this.session.statesByIdentity.get(value)?.kind ?? recognize(this.session.types, value)
      this.kinds.set(value, kind)
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
      dormant: new Map(),
    }
    // The probe settled every negative reachability answer before any discovery work, and no
    // native write happens between the two passes, so discovery reuses those answers instead
    // of reading the unchanged subtrees again.
    const discovery: ObservationPhase = {
      kind: 'discover',
      plan,
      required: this.phase.required,
      values: new WeakMap(),
    }
    this.phase = discovery
    const result = this.materializeContainerSlot(value, false)
    for (const node of plan.closure.facts) {
      const activation = plan.dormant.get(node)
      if (activation === undefined) continue
      plan.dormant.delete(node)
      for (const [index, slot] of activation.slots.entries())
        activation.record.children[index] = this.materializeContainerSlot(
          slot.value,
          slot.currentBacked,
        )
    }
    this.phase = {
      kind: 'sealed',
      required: new WeakMap(),
      values: new WeakMap(),
    }
    const project = plan.clonesSpecialValues || this.accessorObservations !== undefined
    const finalized = project ? this.materializeContainerSlot(value, false) : result
    if (!isObject(finalized)) return finalized
    const { types } = this.session
    const kindOf = (value: object): symbol => this.kindOf(value)
    // Discovery kept unchanged subtrees as fixed leaves. When the kernel cannot keep every
    // settled record, the sealed pass (already current) materializes everything and selects again.
    return (
      restoreIdentities(types, finalized as FinalizedReference, project, kindOf) ??
      restoreIdentities(
        types,
        this.materializeContainerSlot(value, false) as FinalizedReference,
        true,
        kindOf,
      )!
    )
  }

  /**
   * Determines whether reachable draft changes or special values require rebuilding a value.
   *
   * @remarks
   * Records parent dependencies during planning. Negative results are cached only after a complete
   * reachable search finds no changes; a cycle-guard hit alone cannot settle an ancestor.
   */
  private needsMaterialization(
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
    const visited = new Set<object>()
    const result = this.checkMaterialization(value, knownKind, visited)
    // A cycle guard remains provisional until the entire reachable check settles.
    if (!result) for (const node of visited) this.phase.required.set(node, false)
    return result
  }

  /** Checks one reachable value while treating a cycle-guard hit as provisional. */
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
    if (this.materializationPlan?.closure.facts.has(base) === true) {
      return true
    }
    const cached = memo.get(base)

    if (cached !== undefined) {
      return cached
    }

    if (
      state?.modified === true ||
      this.untrackedSpecialsToClone.has(value) ||
      (state === undefined &&
        (this.session.specialCloneCloneToBase.has(value) ||
          this.session.specialCloneBaseToClone.has(value)))
    ) {
      memo.set(base, true)
      return true
    }

    if (visited.has(base)) {
      return false
    }

    visited.add(base)
    // Descendant accessor reads can draft this base and write through it; look its state up again.
    const result =
      this.checkDescendantsForMaterialization(base, state?.kind ?? knownKind, visited) ||
      this.session.statesByIdentity.get(base)?.modified === true ||
      this.accessorObservations?.has(base) === true

    if (result) {
      memo.set(base, true)
    }

    return result
  }

  /** Checks type-declared copy dependencies in their native observation order. */
  private stableSpecialDependencies(value: object, policy: SpecialPolicy): boolean {
    return policy.dependencies(value, (dependency, dependencyKind) => {
      if (this.untrackedSpecialsToClone.has(dependency)) return false
      if (this.session.specialCloneCloneToBase.has(dependency))
        return (
          (this.materializeContainerSlot(dependency, false) as FinalizedReference).target ===
          dependency
        )
      const clone = this.session.specialCloneBaseToClone.get(dependency)
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
    const forced = this.untrackedSpecialsToClone.has(value)
    const dependenciesStable =
      copyBase === undefined && currentBacked && !forced
        ? this.stableSpecialDependencies(value, policy)
        : true
    const equivalent =
      copyBase !== undefined
        ? this.forcedOwnedCopies?.has(value) !== true && policy.equivalent(copyBase, value)
        : copy === undefined || !currentBacked || forced || !dependenciesStable
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
        this.session.specialCloneBaseToClone.get(child) ??
        (this.session.specialCloneCloneToBase.has(child) ? child : undefined)
      if (copy !== undefined && this.forcedOwnedCopies?.has(copy) !== true) {
        ;(this.forcedOwnedCopies ??= new WeakSet()).add(copy)
        this.phase.values.delete(copy)
        const base = this.session.specialCloneCloneToBase.get(copy)
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
    const reference = { leaf, target }
    this.phase.values.set(memoKey, reference)
    return reference
  }

  /** Finalizes a slot using its provenance to distinguish base-backed reuse from replacement values. */
  private materializeContainerSlot(value: unknown, isCurrentBackedSlot: boolean): unknown {
    if (!isObject(value)) {
      return value
    }

    const memo = this.phase.values
    const cached = memo.get(value)

    if (cached !== undefined) {
      return cached
    }

    const draftState = this.session.statesByIdentity.get(value)

    if (draftState !== undefined) {
      return this.materializeState(draftState, value)
    }

    const copyBase = this.session.specialCloneCloneToBase.get(value)
    const copy = this.session.specialCloneBaseToClone.get(value)
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
    const policy = this.session.types.specials[kind]
    if (policy === undefined) {
      const active = this.needsMaterialization(value, kind)
      // The probe settled that nothing below an unchanged object backed by `current`
      // changed, so during discovery it is a fixed leaf kept by identity, without observing,
      // recording or selecting its subtree. Untracked objects keep the record path, whose
      // specials are cloned. If the kernel finds no plan, or a special clone sets the
      // projection, the sealed pass materializes everything.
      if (!active && isCurrentBackedSlot && this.materializationPlan !== undefined)
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
    let record: ReuseNode | undefined
    const plan = this.materializationPlan
    // Dormant records keep their observed slots for later activation; active ones need none.
    const slots: PendingActivation['slots'] | undefined =
      active || plan === undefined ? undefined : []
    this.session.types.structural[kind].observeDraft(
      source,
      (layout) => {
        record = {
          attributes: undefined,
          children: [],
          keys: undefined,
          layout,
          settled: !active,
          target: base ?? source,
        }
        this.phase.values.set(memoKey, record)
        if (plan !== undefined) {
          if (slots === undefined) plan.closure.require(memoKey)
          else plan.dormant.set(memoKey, { record, slots })
        }
      },
      (value, key, backed, attributes) => {
        const currentBacked = backed === true
        if (key !== undefined) (record!.keys ??= []).push(key)
        if (slots !== undefined) slots.push({ currentBacked, value })
        let resolve = true
        if (!active && isObject(value)) {
          // An active parent is already a closure fact; SeededRequirements proves that
          // omitting implications into initial facts preserves the closure.
          if (plan !== undefined)
            plan.closure.imply(this.session.statesByIdentity.get(value)?.base ?? value, memoKey)
          // Unchanged special children of an inactive record stay settled leaves in every phase;
          // unchanged structural children become fixed leaves in materializeContainerSlot.
          if (this.phase.values.get(value) === undefined) {
            const kind = this.kindOf(value)
            if (this.session.types.specials[kind] !== undefined)
              resolve = this.needsMaterialization(value, kind)
          }
        }
        record!.children.push(
          resolve
            ? this.materializeContainerSlot(value, currentBacked)
            : { target: value as object },
        )
        if (attributes !== undefined) (record!.attributes ??= []).push(attributes)
      },
      {
        base,
        properties: state?.properties,
        read: (value, key) => this.readTraversalProperty(value, key, state),
      },
    )
    return record!
  }

  /** Captures one draft state and records whether its slots need semantic resolution. */
  private materializeState(state: DraftState, knownUncachedValue?: object): object {
    const memo = this.phase.values

    if (knownUncachedValue !== state.base) {
      const cached = memo.get(state.base)

      if (cached !== undefined) {
        return cached as object
      }
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
      this.session.specialCloneBaseToClone.has(value) ||
      this.session.specialCloneCloneToBase.has(value) ||
      this.untrackedSpecialsToClone.has(value)
    ) {
      return
    }
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
  private readTraversalProperty(value: object, key: PropertyKey, knownState?: DraftState): unknown {
    const properties = knownState?.properties
    const descriptor =
      properties === undefined
        ? propertyDescriptor(value, key)
        : (properties.ownDescriptor(key) ?? propertyDescriptor(properties.sourcePrototype(), key))
    if (descriptor !== undefined && !('value' in descriptor)) {
      const receiver = knownState?.handle ?? this.session.materializeChild(value)
      const state = knownState ?? this.session.statesByIdentity.get(value)!
      this.accessorObservations ??= new WeakMap()
      let observations = this.accessorObservations.get(state.base)
      if (observations === undefined) {
        observations = new Map()
        this.accessorObservations.set(state.base, observations)
      }
      if (observations.has(key)) return observations.get(key)
      if (this.phase.kind === 'sealed') throw finalizationAccessorUnstable(key)
      const observed = state.properties!.read(key, receiver)
      this.kinds = new Map()
      observations.set(key, observed)
      if (this.materializationPlan !== undefined)
        this.materializationPlan.closure.require(state.base)
      return observed
    }
    return properties === undefined ? (Reflect.get(value, key) as unknown) : properties.read(key)
  }

  /** Visits the kind-specific edge surface until a descendant requires materialization. */
  private checkDescendantsForMaterialization(
    value: object,
    knownKind: symbol | undefined,
    visited: Set<object>,
  ): boolean {
    return this.session.types.policies[knownKind ?? this.kindOf(value)].someChild(
      value,
      (source, key) => this.readTraversalProperty(source, key),
      (child) => this.needsMaterialization(child, undefined, { parent: value, visited }),
    )
  }
}
