import { recognize } from './adapters/recognition'
import { isObject, markLike } from './object-property'
import { storageIdentity } from './adapters/vue'
import { ATOM_KIND } from './constants'
import type {
  DraftContext,
  DraftState,
  DraftStrategy,
  ImmutableRegistry,
  PrototypeRead,
} from './types'
import { Detached } from './standard-prototypes'

const NO_VIEWS: readonly object[] = /* @__PURE__ */ Object.freeze([])

// Held handles retain only recipe state. Observation passes and getter caches
// are owned by a separate finalizer and cannot become reachable through a handle.
export class DraftSession extends Detached implements DraftContext {
  // Created at the first special-value copy; until then no value is a copy or has one.
  declare nativeOwners: WeakMap<object, object> | undefined
  declare specialCloneBaseToClone: WeakMap<object, object> | undefined
  declare specialCloneCloneToBase: WeakMap<object, object> | undefined
  declare readonly statesByIdentity: WeakMap<object, DraftState>
  declare readonly types: ImmutableRegistry
  // The views of each drafted object other than its base, such as its raw object when a Vue proxy
  // of it was drafted first; created on the first.
  declare private views: WeakMap<DraftState, object[]> | undefined
  declare draftLayers?: Map<object, object>
  constructor(types: ImmutableRegistry) {
    super()
    this.types = types
    this.nativeOwners = undefined
    this.specialCloneBaseToClone = undefined
    this.specialCloneCloneToBase = undefined
    this.statesByIdentity = new WeakMap()
    this.views = undefined
  }
  /**
   * Creates a writable special-value copy and registers indirectly cloned dependencies.
   *
   * @remarks
   * Dependencies reuse an existing registered copy, otherwise they are copied through their
   * known kind before the dependent copy is constructed, in the kind's native read order.
   */
  private cloneSpecialValueAfterMiss(
    value: object,
    kind: symbol,
    strategy: Extract<DraftStrategy, { tag: 'copy' }>,
  ): object {
    const links = strategy.links
    if (
      links.tag === 'dependent' &&
      links.writable(value, (dependency) => this.specialCloneCloneToBase?.has(dependency) === true)
    )
      return value

    const specials = this.types.specials
    const resolve = (dependency: object, dependencyKind: symbol): object => {
      const existing = this.specialCloneBaseToClone?.get(dependency)
      if (existing !== undefined) return existing
      const copy = specials[dependencyKind]!.copy(dependency, resolve, this)
      markLike(copy, dependency)
      // A value that is its own copy, such as a `SharedArrayBuffer`, belongs to `current`.
      if (copy !== dependency) Reflect.preventExtensions(copy)
      ;(this.specialCloneBaseToClone ??= new WeakMap()).set(dependency, copy)
      return copy
    }
    // A copy carries only its native content, so like a non-extensible object it refuses a new
    // property instead of accepting one the result would drop (DraftSurface.admits).
    const replacement = specials[kind]!.copy(value, resolve, this)
    // A copy keeps the `markRaw` marker of the value it copies.
    markLike(replacement, value)
    if (replacement !== value) Reflect.preventExtensions(replacement)
    ;(this.specialCloneBaseToClone ??= new WeakMap()).set(value, replacement)
    ;(this.specialCloneCloneToBase ??= new WeakMap()).set(replacement, value)
    if (links.tag === 'dependent')
      links.register(value, replacement, (copy, base) => {
        markLike(copy, base)
        if (copy !== base) Reflect.preventExtensions(copy)
        ;(this.specialCloneCloneToBase ??= new WeakMap()).set(copy, base)
      })
    return replacement
  }

  /** Creates a new handle or special-value copy, preserving non-object values. */
  createDraft<T>(current: T): T {
    if (!isObject(current)) {
      return current
    }

    // Recognition reads the prototype at most once and the handle's target reuses it
    // (Types.Ingress).
    const read: PrototypeRead = { known: false, prototype: null }
    const kind = recognize(this.types, current, read)
    // An atom is not drafted: the recipe reads and changes the value itself.
    if (kind === ATOM_KIND) return current

    const strategy = this.types.drafts[kind]
    if (strategy.tag === 'copy')
      return this.cloneSpecialValueAfterMiss(current, kind, strategy) as T

    // A Vue proxy is a view of its raw object, so the views of one object, the object included,
    // share its one draft. A Vue proxy of a draft, such as `reactive(draft)` that a recipe stored,
    // stands for that draft: drafting it again would wrap the draft in a new draft, and Vue that
    // one in a new proxy, at every read.
    const prototype = read.known ? read.prototype : undefined
    const storage = storageIdentity(current, prototype)
    if (storage !== current) {
      const shared = this.statesByIdentity.get(storage)
      if (shared !== undefined) {
        if (shared.handle !== storage) this.view(current, shared)
        return shared.handle as T
      }
    }
    const state = strategy.state(current, this)
    this.statesByIdentity.set(current, state)
    if (storage !== current) this.view(storage, state)
    const handle = strategy.handle(state, prototype)
    state.handle = handle
    this.statesByIdentity.set(handle, state)
    return handle as T
  }

  /** Resolves a recipe read to its existing handle or isolated special-value copy. */
  materializeChild(value: object): object {
    const existingState = this.statesByIdentity.get(value)
    if (existingState !== undefined) return existingState.handle!
    if (this.specialCloneCloneToBase?.has(value) === true) return value

    const existingClone = this.specialCloneBaseToClone?.get(value)

    if (existingClone !== undefined) {
      return existingClone
    }

    return this.createDraft(value)
  }

  /**
   * The draft of `value`, or of the object `value` views when the recipe drafted it through another
   * view, which this records for `value`: a Vue proxy and its raw object share one draft.
   */
  stateOf(value: object): DraftState | undefined {
    const state = this.statesByIdentity.get(value)
    if (state !== undefined) return state
    const storage = storageIdentity(value)
    if (storage === value) return undefined
    const shared = this.statesByIdentity.get(storage)
    // A Vue proxy of a draft is not a view of the drafted object.
    if (shared === undefined || shared.handle === storage) return undefined
    this.view(value, shared)
    return shared
  }

  /** Records `value` as a view of the object `state` drafts, other than its base. */
  private view(value: object, state: DraftState): void {
    this.statesByIdentity.set(value, state)
    const views = (this.views ??= new WeakMap()).get(state)
    if (views === undefined) this.views.set(state, [value])
    else views.push(value)
  }

  /** The views of the object `state` drafts other than its base, such as its raw object. */
  viewsOf(state: DraftState): readonly object[] {
    return this.views?.get(state) ?? NO_VIEWS
  }

  /** The draft that `value`, a Vue proxy of a draft such as `reactive(draft)`, wraps, if any. */
  wrappedDraft(value: object): object | undefined {
    const storage = storageIdentity(value)
    return storage !== value && this.statesByIdentity.get(storage)?.handle === storage
      ? storage
      : undefined
  }

  copyBase(value: object): object | undefined {
    return this.specialCloneCloneToBase?.get(value)
  }

  copyOf(value: object): object | undefined {
    return this.specialCloneBaseToClone?.get(value)
  }

  /** Compares structural handles through their bases while keeping special copies distinct. */
  isSameDraftValue(currentValue: unknown, value: unknown): boolean {
    // Structural handles represent their bases; special writable clones remain distinct values.
    const currentBase = isObject(currentValue)
      ? (this.statesByIdentity.get(currentValue)?.base ?? currentValue)
      : currentValue
    const assignedBase = isObject(value) ? (this.statesByIdentity.get(value)?.base ?? value) : value
    return Object.is(currentBase, assignedBase)
  }
}
