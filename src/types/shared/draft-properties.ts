import { isObject, ownKeys } from '../../object-property'
import { draftDefinePropertyUnsupported } from '../../error'
import { propertyDescriptor } from '../../object-property'
import type { BaseDraftState, DraftContext, PropertyDraftPort } from '../../types'

// V8 keeps a null-prototype object in dictionary mode; a store behind an empty frozen
// prototype keeps fast properties, so slot reads and key listing stay on the fast path.
const STORE_PROTOTYPE: object = /* @__PURE__ */ Object.freeze(Object.create(null) as object)

/**
 * Captures the descriptor store at the first-copy observation boundary.
 *
 * @remarks
 * Preserves prototype capture, key order, wrapper-visible reads, and native array-length effects.
 * The store becomes visible to the state only after capture finishes.
 */
function preparePropertyCopy(state: PropertyDraftState): Record<PropertyKey, PropertyDescriptor> {
  if (state.copy !== undefined) return state.copy
  const source = state.base as Record<PropertyKey, unknown>
  const prototype = Object.getPrototypeOf(source) as object | null
  const replacement = Object.create(STORE_PROTOTYPE) as Record<PropertyKey, PropertyDescriptor>
  state.rules.initialize(source, replacement)
  for (const key of ownKeys(source)) {
    const descriptor = Object.getOwnPropertyDescriptor(source, key)
    if (descriptor === undefined) continue
    // Capture wrapper-exposed values in the same order as the former physical copy.
    if ('value' in descriptor) descriptor.value = source[key]
    state.rules.capture(replacement, key, descriptor)
    replacement[key] = descriptor
  }
  state.copyPrototype = prototype
  state.copy = replacement
  return replacement
}

/**
 * Applies a data-property write and records effective or partially completed array changes.
 *
 * @remarks
 * Accessor dispatch and explicit receiver selection happen in the proxy's set trap. This helper
 * rechecks the captured own descriptor after first-copy observations before mutating it.
 */
function writeProperty(
  state: PropertyDraftState,
  property: PropertyKey,
  value: unknown,
  descriptor: PropertyDescriptor | undefined,
): boolean {
  if (descriptor !== undefined) {
    if (!('value' in descriptor) || descriptor.writable === false) return false
    if (state.context.isSameDraftValue(state.read(property), value)) return true
  }
  const copy = preparePropertyCopy(state)
  const written = state.rules.write(state, copy, property, value)
  if (written) state.modified = true
  return written
}

/**
 * Implements object and array draft reads, reflection, and writes over a logical descriptor store.
 *
 * @remarks
 * The first copy captures descriptors and wrapper-visible data values eagerly. Internal reads
 * borrow those descriptors; public reflection returns separate descriptors containing draft-safe
 * values. The proxy uses a separate extensible target to preserve native proxy invariants.
 * Held handles keep their working state after finalization and are not revoked.
 * @internal
 */
export class PropertyDraftState<K extends symbol = symbol>
  implements BaseDraftState, PropertyDraftPort, ProxyHandler<object>
{
  declare readonly base: object
  declare readonly context: DraftContext
  declare copy: Record<PropertyKey, PropertyDescriptor> | undefined
  declare copyPrototype: object | null | undefined
  declare handle: object | undefined
  declare readonly kind: K
  declare modified: boolean
  declare readonly properties: this
  declare readonly rules: PropertyDraftRules<K>

  source(): object {
    return this.base
  }

  /** Binds the base and call context without observing or copying properties. */
  constructor(base: object, context: DraftContext, rules: PropertyDraftRules<K>) {
    this.base = base
    this.context = context
    this.copy = undefined
    this.copyPrototype = undefined
    this.handle = undefined
    this.kind = rules.kind
    this.modified = false
    this.properties = this
    this.rules = rules
  }
  /** Tests own and inherited presence through the current descriptor store. */
  contains(property: PropertyKey): boolean {
    if (this.copy === undefined) return property in this.base
    if (this.copy[property] !== undefined) return true
    const prototype = this.sourcePrototype()
    return prototype !== null && property in prototype
  }
  /** Rejects reflective definitions, which are outside the draft mutation surface. */
  defineProperty(_target: object, property: PropertyKey): never {
    throw draftDefinePropertyUnsupported(property)
  }
  /** Deletes a configurable own entry and records the change. */
  deleteProperty(_target: object, property: PropertyKey): boolean {
    if (this.ownDescriptor(property) === undefined) return true
    const copy = preparePropertyCopy(this)
    if (copy[property]?.configurable === false) return false
    delete copy[property]
    this.modified = true
    return true
  }
  /** Wraps object-valued reads while preserving ordinary getter receiver behavior. */
  get(_target: object, property: PropertyKey, receiver: unknown): unknown {
    // The presence check precedes the read: inherited `has` traps may introduce the property.
    const hasProperty = this.contains(property)
    const value = this.read(property, receiver)
    return !hasProperty || !isObject(value) ? value : this.context.materializeChild(value)
  }
  /** Returns a separate descriptor whose data value follows ordinary draft reads. */
  getOwnPropertyDescriptor(_target: object, property: PropertyKey): PropertyDescriptor | undefined {
    const ownDescriptor = this.ownDescriptor(property)
    if (ownDescriptor === undefined) return undefined
    const descriptor = { ...ownDescriptor }
    if ('value' in descriptor) descriptor.value = Reflect.get(this.handle!, property) as unknown
    descriptor.configurable = this.rules.configurable(property)
    if (!descriptor.configurable) descriptor.writable = true
    return descriptor
  }
  /** Exposes the base prototype independently of the captured copy prototype. */
  getPrototypeOf(): object | null {
    return Object.getPrototypeOf(this.base) as object | null
  }
  /** Exposes the same presence rules as ordinary draft reads. */
  has(_target: object, property: PropertyKey): boolean {
    return this.contains(property)
  }
  // The private descriptor store has ordinary own-key ordering; a user source
  // retains the separate string/symbol observations used by finalization.
  keys(source: object): PropertyKey[] {
    return ownKeys(this.copy ?? source)
  }
  /** Borrows the current own descriptor for internal inspection. */
  ownDescriptor(property: PropertyKey): PropertyDescriptor | undefined {
    if (this.copy === undefined) return Object.getOwnPropertyDescriptor(this.base, property)
    // Internal callers borrow this record; public reflection copies before changing it.
    return this.copy[property]
  }
  /** Enumerates the current store with native string and symbol ordering. */
  ownKeys(): Array<string | symbol> {
    return Reflect.ownKeys(this.copy ?? this.base)
  }
  /** Reads the logical value with the supplied getter receiver, without wrapping children. */
  read(property: PropertyKey, receiver: unknown = this.base): unknown {
    if (this.copy === undefined) return Reflect.get(this.base, property, receiver) as unknown
    const descriptor = this.copy[property]
    if (descriptor !== undefined)
      return 'value' in descriptor
        ? (descriptor.value as unknown)
        : (descriptor.get?.call(receiver) as unknown)
    const prototype = this.sourcePrototype()
    return prototype === null ? undefined : (Reflect.get(prototype, property, receiver) as unknown)
  }
  /** Dispatches setters and routes data writes to the explicitly selected receiver. */
  set(_target: object, property: PropertyKey, value: unknown, receiver: unknown): boolean {
    const ownDescriptor = this.ownDescriptor(property)
    const descriptor = ownDescriptor ?? propertyDescriptor(this.sourcePrototype(), property)
    if (descriptor !== undefined && !('value' in descriptor)) {
      if (descriptor.set === undefined) return false
      descriptor.set.call(receiver, value)
      return true
    }
    if (descriptor?.writable === false) return false
    if (receiver !== this.handle) {
      const receiverState = isObject(receiver)
        ? this.context.statesByIdentity.get(receiver)
        : undefined
      if (
        receiverState !== undefined &&
        receiverState.base !== receiver &&
        receiverState instanceof PropertyDraftState
      )
        return writeProperty(
          receiverState as PropertyDraftState,
          property,
          value,
          receiverState.ownDescriptor(property),
        )
      // Delegate the ordinary data-descriptor receiver transition to the engine.
      return Reflect.set({ [property]: undefined }, property, value, receiver)
    }
    return writeProperty(this, property, value, ownDescriptor)
  }
  /** Uses the captured prototype after first copy, otherwise observes the base. */
  sourcePrototype(): object | null {
    return this.copy === undefined
      ? (Object.getPrototypeOf(this.base) as object | null)
      : this.copyPrototype!
  }
}

/**
 * Creates the native proxy for a newly allocated object or array state.
 *
 * @remarks
 * The draft session installs and registers the returned identity after construction.
 * @internal
 */
export function createPropertyHandle(state: PropertyDraftState): object {
  const target = state.rules.target(state.base)

  return new Proxy(target, state)
}

/** Stores borrowed native descriptors under ordinary own-property keys. */
export type DescriptorStore = Record<PropertyKey, PropertyDescriptor>

/** Type-owned native rules over the shared descriptor store and proxy protocol. */
export interface PropertyDraftRules<K extends symbol = symbol> {
  readonly kind: K
  readonly capture: (
    copy: DescriptorStore,
    key: PropertyKey,
    descriptor: PropertyDescriptor,
  ) => void
  readonly configurable: (key: PropertyKey) => boolean
  readonly initialize: (source: Record<PropertyKey, unknown>, copy: DescriptorStore) => void
  readonly target: (base: object) => object
  readonly write: (
    state: PropertyDraftState,
    copy: DescriptorStore,
    key: PropertyKey,
    value: unknown,
  ) => boolean
}

/** Updates a logical data slot after the type-owned constraints have accepted it. */
export function writeDataSlot(
  copy: DescriptorStore,
  property: PropertyKey,
  value: unknown,
): boolean {
  const descriptor = copy[property]
  if (descriptor !== undefined && (!('value' in descriptor) || descriptor.writable === false))
    return false
  if (descriptor === undefined)
    copy[property] = { configurable: true, enumerable: true, value, writable: true }
  else descriptor.value = value
  return true
}
