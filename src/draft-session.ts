import { recognize } from './adapters/recognition'
import { isObject } from './object-property'
import type { DraftContext, DraftState, DraftStrategy, ImmutableRegistry } from './types'

// Held handles retain only recipe state. Observation passes and getter caches
// are owned by a separate finalizer and cannot become reachable through a handle.
export class DraftSession implements DraftContext {
  declare readonly specialCloneBaseToClone: WeakMap<object, object>
  declare readonly specialCloneCloneToBase: WeakMap<object, object>
  declare readonly statesByIdentity: WeakMap<object, DraftState>
  declare readonly types: ImmutableRegistry
  declare nativeOwners?: WeakMap<object, object>
  constructor(types: ImmutableRegistry) {
    this.types = types
    this.specialCloneBaseToClone = new WeakMap()
    this.specialCloneCloneToBase = new WeakMap()
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
      links.writable(value, (dependency) => this.specialCloneCloneToBase.has(dependency))
    )
      return value

    const specials = this.types.specials
    const resolve = (dependency: object, dependencyKind: symbol): object => {
      const existing = this.specialCloneBaseToClone.get(dependency)
      if (existing !== undefined) return existing
      const copy = specials[dependencyKind]!.copy(dependency, resolve, this)
      this.specialCloneBaseToClone.set(dependency, copy)
      return copy
    }
    const replacement = specials[kind]!.copy(value, resolve, this)
    this.specialCloneBaseToClone.set(value, replacement)
    this.specialCloneCloneToBase.set(replacement, value)
    if (links.tag === 'dependent')
      links.register(value, replacement, (copy, base) => {
        this.specialCloneCloneToBase.set(copy, base)
      })
    return replacement
  }

  /** Creates a new handle or special-value copy, preserving non-object values. */
  createDraft<T>(current: T): T {
    if (!isObject(current)) {
      return current
    }

    const kind = recognize(this.types, current)

    const strategy = this.types.drafts[kind]
    if (strategy.tag === 'copy')
      return this.cloneSpecialValueAfterMiss(current, kind, strategy) as T

    const state = strategy.state(current, this)
    this.statesByIdentity.set(current, state)
    const handle = strategy.handle(state)
    state.handle = handle
    this.statesByIdentity.set(handle, state)
    return handle as T
  }

  /** Resolves a recipe read to its existing handle or isolated special-value copy. */
  materializeChild(value: object): object {
    const existingState = this.statesByIdentity.get(value)
    if (existingState !== undefined) return existingState.handle!
    if (this.specialCloneCloneToBase.has(value)) return value

    const existingClone = this.specialCloneBaseToClone.get(value)

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
