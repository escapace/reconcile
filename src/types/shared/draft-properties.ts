import { storageIdentity } from '../../adapters/vue'
import { hasOwn, isObject, ownKeys } from '../../object-property'
import { draftDefinePropertyUnsupported } from '../../error'
import { propertyDescriptor } from '../../object-property'
import type { BaseDraftState, DraftContext, PropertyDraftPort } from '../../types'
import {
  type DataDescriptor,
  accessorDescriptor,
  dataDescriptor,
  Detached,
  isDataDescriptor,
} from '../../standard-prototypes'

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
function preparePropertyCopy(
  state: PropertyDraftState,
  known?: PropertyKey,
  knownDescriptor?: PropertyDescriptor,
  knownValue?: unknown,
): Record<PropertyKey, PropertyDescriptor> {
  if (state.copy !== undefined) return state.copy
  const source = state.base as Record<PropertyKey, unknown>
  const prototype = Object.getPrototypeOf(source) as object | null
  const replacement = Object.create(STORE_PROTOTYPE) as Record<PropertyKey, PropertyDescriptor>
  state.rules.initialize(source, replacement)
  for (const key of ownKeys(source)) {
    // The write that makes this copy already read its key's own data descriptor and value.
    const reused = key === known && knownDescriptor !== undefined
    const descriptor = reused ? knownDescriptor : Object.getOwnPropertyDescriptor(source, key)
    if (descriptor === undefined) continue
    // Capture wrapper-exposed values in the same order as the former physical copy.
    if (isDataDescriptor(descriptor)) descriptor.value = reused ? knownValue : source[key]
    state.rules.capture(replacement, key, descriptor)
    replacement[key] = descriptor
  }
  state.copyPrototype = prototype
  state.copy = replacement
  return replacement
}

const ASSIGNED_FLAGS = ['writable', 'enumerable', 'configurable'] as const

/** Whether a definition's descriptor is the one assignment makes: own data, writable,
 * enumerable and configurable, with no field read through `Object.prototype`. */
function assignedData(descriptor: PropertyDescriptor): boolean {
  for (let index = 0; index < ASSIGNED_FLAGS.length; index += 1) {
    const flag = ASSIGNED_FLAGS[index]
    if (!hasOwn(descriptor, flag) || descriptor[flag] !== true) return false
  }
  return hasOwn(descriptor, 'value')
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
  let current: unknown
  if (descriptor !== undefined) {
    if (!isDataDescriptor(descriptor) || descriptor.writable === false) return false
    current = state.ownValue(property, descriptor)
    if (state.context.isSameDraftValue(current, value)) return true
  }
  // A non-extensible object, such as a frozen or sealed one, refuses a new property.
  else if (!Object.isExtensible(state.base)) return false
  const copy = preparePropertyCopy(state, property, descriptor, current)
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
  extends Detached
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
  declare private provided: ReadonlyMap<unknown, unknown> | undefined
  // The data descriptor this proxy's getOwnPropertyDescriptor trap returns, reused: the trap
  // fills it after its last call into other code, the engine reads it as the trap returns, and it
  // inherits nothing.
  declare private reported: DataDescriptor | undefined
  // The key whose inherited setter is running with this draft as receiver; its definition of
  // that key is the one reflective definition the draft accepts.
  declare readonly rules: PropertyDraftRules<K>
  declare private settingThrough: PropertyKey | undefined

  source(): object {
    return this.base
  }

  /** Binds the base and call context without observing or copying properties. */
  constructor(base: object, context: DraftContext, rules: PropertyDraftRules<K>) {
    super()
    this.base = base
    this.context = context
    this.copy = undefined
    this.copyPrototype = undefined
    this.handle = undefined
    this.kind = rules.kind
    this.modified = false
    this.properties = this
    this.reported = undefined
    this.settingThrough = undefined
    this.rules = rules
  }
  /** Tests own presence on the object or its working copy, then inherited presence on the
   * prototype. */
  contains(property: PropertyKey): boolean {
    return this.owns(property) || this.inherits(property)
  }
  /** Whether the prototype the draft reports has the property. */
  private inherits(property: PropertyKey): boolean {
    const prototype = this.sourcePrototype()
    return prototype !== null && property in prototype
  }
  /** Whether the object, or after the first write its working copy, owns the property. */
  private owns(property: PropertyKey): boolean {
    return this.copy === undefined ? hasOwn(this.base, property) : this.copy[property] !== undefined
  }
  /**
   * Assigns through an accessor, own or inherited. While an inherited setter runs with this draft
   * as receiver, the draft accepts that setter's definition of the key (`defineProperty`).
   */
  private setThrough(
    descriptor: PropertyDescriptor,
    property: PropertyKey,
    value: unknown,
    receiver: unknown,
    inherited: boolean,
  ): boolean {
    if (descriptor.set === undefined) return false
    if (!inherited || receiver !== this.handle) {
      descriptor.set.call(receiver, value)
      return true
    }
    const outer = this.settingThrough
    this.settingThrough = property
    try {
      descriptor.set.call(receiver, value)
    } finally {
      this.settingThrough = outer
    }
    return true
  }
  /**
   * Rejects reflective definitions, which are outside the draft mutation surface, except the one
   * an inherited setter makes while this draft assigns the key: the key defined as assignment
   * would, while the draft lacks it, as `node --frozen-intrinsics` and SES setters do.
   * `PropertyWrite.draftThroughSetter` is this decision.
   */
  defineProperty(_target: object, property: PropertyKey, descriptor: PropertyDescriptor): boolean {
    if (
      property !== this.settingThrough ||
      !assignedData(descriptor) ||
      this.ownDescriptor(property) !== undefined
    )
      throw draftDefinePropertyUnsupported(property)
    this.settingThrough = undefined
    return writeProperty(this, property, descriptor.value, undefined)
  }
  /** Deletes a configurable own entry the result could carry and records the change. */
  deleteProperty(_target: object, property: PropertyKey): boolean {
    if (this.ownDescriptor(property) === undefined) return true
    if (!this.rules.admits(property)) return false
    const copy = preparePropertyCopy(this)
    if (copy[property]?.configurable === false) return false
    delete copy[property]
    this.modified = true
    return true
  }
  /** Wraps object-valued reads while preserving ordinary getter receiver behavior. */
  get(_target: object, property: PropertyKey, receiver: unknown): unknown {
    // An own store entry decides presence privately, so one store read serves both steps.
    const descriptor = this.copy?.[property]
    if (descriptor !== undefined) {
      const value = isDataDescriptor(descriptor)
        ? (descriptor.value as unknown)
        : (descriptor.get?.call(receiver) as unknown)
      return !isObject(value) ? value : this.context.materializeChild(value)
    }
    // Before the first write an own property is read through the object; any other property
    // comes from the prototype, before and after it, so a wrapper of the object never answers a
    // property the object does not own (DraftRead.read).
    if (this.copy === undefined && hasOwn(this.base, property)) {
      const value = Reflect.get(this.base, property, receiver) as unknown
      return !isObject(value) ? value : this.context.materializeChild(value)
    }
    // The presence check precedes the read: inherited `has` traps may introduce the property.
    // The trap can also add the property to the draft, so the read decides the source again.
    const present = this.inherits(property)
    const value = this.read(property, receiver)
    // A native method the draft replaces resolves to its replacement; an override of it, in a
    // subclass or on the object, still runs (DraftMembers).
    if (typeof value === 'function' && this.rules.methods !== undefined)
      return (this.provided ??= this.rules.methods(this.context, this.base)).get(value) ?? value
    return !present || !isObject(value) ? value : this.context.materializeChild(value)
  }
  /** Returns a separate descriptor whose data value follows ordinary draft reads. */
  getOwnPropertyDescriptor(_target: object, property: PropertyKey): PropertyDescriptor | undefined {
    const ownDescriptor = this.ownDescriptor(property)
    if (ownDescriptor === undefined) return undefined
    const configurable = this.rules.configurable(property)
    if (isDataDescriptor(ownDescriptor)) {
      // The read can run code that reenters this trap, so the shared descriptor is filled after it.
      const value = Reflect.get(this.handle!, property) as unknown
      const reported = (this.reported ??= dataDescriptor())
      reported.configurable = configurable
      reported.enumerable = ownDescriptor.enumerable === true
      reported.value = value
      reported.writable = !configurable || ownDescriptor.writable === true
      return reported
    }
    return accessorDescriptor(ownDescriptor, configurable)
  }
  /** Exposes the base prototype independently of the captured copy prototype. */
  getPrototypeOf(): object | null {
    return Object.getPrototypeOf(this.base) as object | null
  }
  /** Refuses to make the draft non-extensible, as `Object.freeze` and `Object.seal` would. */
  preventExtensions(): boolean {
    return false
  }
  /** Refuses a prototype change; setting the prototype the draft reports is a no-op. */
  setPrototypeOf(_target: object, prototype: object | null): boolean {
    return prototype === this.getPrototypeOf()
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
  /**
   * The value of an own data property whose descriptor the caller just read from this draft's
   * store, without asking again whether the draft owns it.
   */
  ownValue(property: PropertyKey, descriptor: PropertyDescriptor): unknown {
    return this.copy === undefined
      ? (Reflect.get(this.base, property) as unknown)
      : (descriptor.value as unknown)
  }
  /** Whether reads still go to the object itself, before the first write. */
  readsBase(): boolean {
    return this.copy === undefined
  }
  /** Reads the logical value with the supplied getter receiver, without wrapping children. */
  read(property: PropertyKey, receiver: unknown = this.base): unknown {
    if (this.copy === undefined) {
      if (hasOwn(this.base, property)) return Reflect.get(this.base, property, receiver) as unknown
    } else {
      const descriptor = this.copy[property]
      if (descriptor !== undefined)
        return isDataDescriptor(descriptor)
          ? (descriptor.value as unknown)
          : (descriptor.get?.call(receiver) as unknown)
    }
    return this.inheritedValue(property, receiver)
  }
  /** Reads a property the draft does not own from the prototype it reports. */
  private inheritedValue(property: PropertyKey, receiver: unknown): unknown {
    const prototype = this.sourcePrototype()
    return prototype === null ? undefined : (Reflect.get(prototype, property, receiver) as unknown)
  }
  /** Dispatches setters and routes data writes to the explicitly selected receiver. */
  set(_target: object, property: PropertyKey, value: unknown, receiver: unknown): boolean {
    const ownDescriptor = this.ownDescriptor(property)
    const descriptor = ownDescriptor ?? propertyDescriptor(this.sourcePrototype(), property)
    if (descriptor !== undefined && !isDataDescriptor(descriptor))
      return this.setThrough(descriptor, property, value, receiver, ownDescriptor === undefined)
    if (descriptor?.writable === false) return false
    // A Vue proxy of this draft, such as `reactive(draft)`, passes itself as the receiver.
    if (
      receiver !== this.handle &&
      (!isObject(receiver) || storageIdentity(receiver) !== this.handle)
    ) {
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
export function createPropertyHandle(state: PropertyDraftState, prototype?: object | null): object {
  const target = state.rules.target(state.base, prototype)

  return new Proxy(target, state)
}

/** Stores borrowed native descriptors under ordinary own-property keys. */
export type DescriptorStore = Record<PropertyKey, PropertyDescriptor>

/** Type-owned native rules over the shared descriptor store and proxy protocol. */
export interface PropertyDraftRules<K extends symbol = symbol> {
  readonly kind: K
  /** Replacements for inherited native methods, keyed by the native function, built once per
   * draft. */
  readonly methods:
    ((context: DraftContext, base: object) => ReadonlyMap<unknown, unknown>) | undefined
  /** Whether the result can carry an own property with this key; DraftSurface.admits. */
  readonly admits: (key: PropertyKey) => boolean
  readonly capture: (
    copy: DescriptorStore,
    key: PropertyKey,
    descriptor: PropertyDescriptor,
  ) => void
  readonly configurable: (key: PropertyKey) => boolean
  readonly initialize: (source: Record<PropertyKey, unknown>, copy: DescriptorStore) => void
  /** The proxy target; `prototype` is the base's prototype when ingress read it. */
  readonly target: (base: object, prototype: object | null | undefined) => object
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
  if (descriptor !== undefined && (!isDataDescriptor(descriptor) || descriptor.writable === false))
    return false
  if (descriptor === undefined)
    copy[property] = { configurable: true, enumerable: true, value, writable: true }
  else descriptor.value = value
  return true
}
