import { recognize } from './adapters/recognition'
import { isObject } from './object-property'
import { ATOM_KIND } from './constants'
import type {
  DraftContext,
  DraftState,
  DraftStrategy,
  ImmutableRegistry,
  PrototypeRead,
} from './types'
import { Detached } from './standard-prototypes'

// Held handles retain only recipe state. Observation passes and getter caches
// are owned by a separate finalizer and cannot become reachable through a handle.
export class DraftSession extends Detached implements DraftContext {
  // Created at the first special-value copy; until then no value is a copy or has one.
  declare nativeOwners: WeakMap<object, object> | undefined
  declare specialCloneBaseToClone: WeakMap<object, object> | undefined
  declare specialCloneCloneToBase: WeakMap<object, object> | undefined
  declare readonly statesByIdentity: WeakMap<object, DraftState>
  declare readonly types: ImmutableRegistry
  declare draftLayers?: Map<object, object>
  constructor(types: ImmutableRegistry) {
    super()
    this.types = types
    this.nativeOwners = undefined
    this.specialCloneBaseToClone = undefined
    this.specialCloneCloneToBase = undefined
    this.statesByIdentity = new WeakMap()
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
      Reflect.preventExtensions(copy)
      ;(this.specialCloneBaseToClone ??= new WeakMap()).set(dependency, copy)
      return copy
    }
    // A copy carries only its native content, so like a non-extensible object it refuses a new
    // property instead of accepting one the result would drop (DraftSurface.admits).
    const replacement = specials[kind]!.copy(value, resolve, this)
    Reflect.preventExtensions(replacement)
    ;(this.specialCloneBaseToClone ??= new WeakMap()).set(value, replacement)
    ;(this.specialCloneCloneToBase ??= new WeakMap()).set(replacement, value)
    if (links.tag === 'dependent')
      links.register(value, replacement, (copy, base) => {
        Reflect.preventExtensions(copy)
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

    const state = strategy.state(current, this)
    this.statesByIdentity.set(current, state)
    const handle = strategy.handle(state, read.known ? read.prototype : undefined)
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
