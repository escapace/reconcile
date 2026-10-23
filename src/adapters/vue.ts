import { draftWrapperIdentityChanged, draftWrapperIteratorMismatched } from '../error'
import { isObject } from '../object-property'
import type { ExposureFacet, ExposureObservation, KeyedCollection } from '../types'
import { Detached, isDataDescriptor } from '../standard-prototypes'

/** Reads wrapper markers without invoking an accessor declared as application data. */
function marker(value: object, key: string, prototype?: object | null): unknown {
  // Ordinary getters using these names are application data, not a wrapper protocol.
  // `Object.prototype` has an immutable prototype, null, so the walk ends there without a read.
  // The value's own prototype is the one a caller already read, when it passes it.
  for (
    let owner: object | null = value;
    owner !== null;
    owner =
      owner === Object.prototype
        ? null
        : owner === value && prototype !== undefined
          ? prototype
          : (Object.getPrototypeOf(owner) as object | null)
  ) {
    const descriptor = Object.getOwnPropertyDescriptor(owner, key)
    if (descriptor !== undefined)
      return isDataDescriptor(descriptor) ? (descriptor.value as unknown) : undefined
  }
  // Vue exposes virtual markers through its get trap, without own descriptors.
  return Reflect.get(value, key) as unknown
}

/**
 * Resolves the backing object of recognized Vue wrappers for storage ownership checks.
 *
 * @remarks
 * Visible wrapper identity remains distinct from backing storage. Ordinary objects identify
 * their own storage. Cyclic marker chains return the original object. This boundary contains
 * no DeepSignal detection, registration, or runtime hook.
 *
 * @returns The unwrapped backing object, or the original object when no valid chain resolves.
 * @internal
 */
export function storageIdentity(value: object, prototype?: object | null): object {
  return resolveStorage(value, prototype, marker(value, '__v_raw', prototype))
}

/**
 * {@link storageIdentity} of a `Map` or `Set`, with fewer reads.
 *
 * @remarks
 * When no object on the collection's chain has `__v_raw`, which `in` asks without running a getter
 * and which Vue's collection proxies, trapping only reads, answer from their raw object, the marker
 * walk would end by reading `__v_raw`; that one read stands for the walk. Both are written as
 * operators, which the engine caches per receiver shape, not as `Reflect` calls, which it does not.
 * @internal
 */
export function collectionIdentity(value: object, prototype?: object | null): object {
  return resolveStorage(
    value,
    prototype,
    '__v_raw' in value
      ? marker(value, '__v_raw', prototype)
      : (value as { readonly __v_raw?: unknown }).__v_raw,
  )
}

// Follows raw markers from `value`, whose own `__v_raw` marker is `first`.
function resolveStorage(
  value: object,
  prototype: object | null | undefined,
  first: unknown,
): object {
  let current = value
  let raw = first
  let seen: Set<object> | undefined
  for (;;) {
    // A prototype the caller read belongs to `value`, not to a raw object it leads to.
    const known = current === value ? prototype : undefined
    if (
      !isObject(raw) ||
      raw === current ||
      (marker(current, '__v_isReactive', known) !== true &&
        marker(current, '__v_isReadonly', known) !== true)
    )
      break
    seen ??= new Set([value])
    if (seen.has(raw)) return value
    seen.add(raw)
    current = raw
    raw = marker(current, '__v_raw')
  }
  return current
}

/**
 * The object members of one Vue collection by raw object, rebuilt when the collection or its
 * revision changes.
 *
 * @remarks
 * Bounded per-call state of one draft: the draft bumps `revision` whenever it adds or removes a
 * member or key, so a lookup never answers from a stale index.
 */
export interface WrappedIndex {
  built:
    { readonly members: Map<object, object>; readonly revision: number; source: object } | undefined
  revision: number
  /** Whether the draft's object is Vue reactive state, read once. */
  vue: boolean | undefined
}

/**
 * Finds the member of a Vue collection copy that `value` is a form of.
 *
 * @remarks
 * Vue collection copies retain iterated identities but need explicit wrapper equivalence for
 * lookup. Native collections never gain that equivalence. Only object members can match an object
 * identity, so undefined unambiguously means miss. The first member with a raw object wins, as a
 * walk in insertion order finds it; `keys` walks them as the built-in methods do.
 */
export function resolveWrappedCollectionMember(
  source: KeyedCollection,
  value: object,
  base: object,
  index: WrappedIndex,
  keys: (source: KeyedCollection) => Iterable<unknown>,
): object | undefined {
  if (storageIdentity(base) === base) return undefined
  let built = index.built
  if (built?.source !== source || built.revision !== index.revision) {
    const members = new Map<object, object>()
    for (const entry of keys(source))
      if (isObject(entry)) {
        const raw = storageIdentity(entry)
        if (!members.has(raw)) members.set(raw, entry)
      }
    built = index.built = { members, revision: index.revision, source }
  }
  return built.members.get(storageIdentity(value))
}

// The caller supplies an optional resolved identity, not draft state or a callback.
// Native collections keep the original value, including any stored draft handle.
// Vue uses the resolved identity so it never wraps an untracked draft handle.
export function normalizeCollectionInsertion(
  base: object,
  value: unknown,
  resolvedIdentity: object | undefined,
  exposure: Extract<ExposureFacet, { tag: 'collection' }>,
  unwrap: boolean,
): unknown {
  if (!isObject(value)) return value
  const raw = storageIdentity(base)
  if (raw === base) return value

  const identity = resolvedIdentity ?? value
  // New Vue Map keys are stored raw, even in shallow collections. Set members
  // and Map values retain explicitly supplied shallow/readonly wrappers instead.
  const inserted = unwrap ? storageIdentity(identity) : identity

  // Reproduce exposure through the wrapper's own iterator and an isolated singleton.
  // Preserve shallow/readonly layers without importing Vue or writing live storage.
  const layers: object[] = [base]
  for (let layer = marker(base, '__v_raw'); layer !== raw; layer = marker(layer, '__v_raw')) {
    if (!isObject(layer) || layers.includes(layer)) throw draftWrapperIdentityChanged()
    layers.push(layer)
  }

  let receiver = exposure.singleton(inserted)
  for (let index = layers.length - 1; index >= 0; index -= 1) {
    const layer = layers[index] as KeyedCollection
    const next = {
      __v_raw: receiver,
      keys() {
        return layer.keys.call(this)
      },
    }
    receiver = next
  }
  const iterator = receiver.keys()
  const entry = iterator.next()
  if (
    entry.done === true ||
    !isObject(entry.value) ||
    storageIdentity(entry.value) !== storageIdentity(inserted) ||
    iterator.next().done !== true
  )
    throw draftWrapperIteratorMismatched()
  return entry.value
}

/** The exposure mode of Vue's deep `reactive` proxy over its storage (`classifyExposure`). */
export const REACTIVE_MODE = 1

/** Whether Vue's reactive `get` trap returns a property's value as stored, without wrapping it. */
export const unwrappedKey = (key: PropertyKey | undefined): boolean =>
  key === '__proto__' || key === '__v_isRef' || key === '__isVue'

/** Classifies the finite raw/Vue exposure palette without constructing wrappers. */
export function exposureMode(
  value: object,
  exposureOf: (value: object) => ExposureFacet,
): number | undefined {
  const storage = storageIdentity(value)
  return storage === value ? 0 : classifyExposure(value, storage, exposureOf(value))
}

// Vue collection traps omit __v_isShallow. Observe that layer's key wrapping on
// private singleton storage, following the existing collection insertion adapter.
function shallowExposure(value: object, exposure: ExposureFacet): boolean | undefined {
  const shallow = marker(value, '__v_isShallow')
  if (typeof shallow === 'boolean') return shallow
  if (exposure.tag !== 'collection') return false
  const probe = {}
  const singleton = exposure.singleton(probe)
  const iterator = (value as KeyedCollection).keys.call({ __v_raw: singleton }) as Iterator<unknown>
  const first = iterator.next()
  if (
    first.done === true ||
    !isObject(first.value) ||
    storageIdentity(first.value) !== probe ||
    iterator.next().done !== true
  )
    return undefined
  return first.value === probe
}

function classifyExposure(
  value: object,
  storage: object,
  exposure: ExposureFacet,
): number | undefined {
  if (storage === value) return 0
  const raw = marker(value, '__v_raw')
  const readonly = marker(value, '__v_isReadonly') === true
  const reactive = marker(value, '__v_isReactive') === true
  const shallow = shallowExposure(value, exposure)
  if (readonly === reactive || shallow === undefined) return undefined
  if (raw === storage) return (readonly ? 3 : 1) + Number(shallow)
  if (
    !readonly ||
    !isObject(raw) ||
    marker(raw, '__v_raw') !== storage ||
    marker(raw, '__v_isReactive') !== true ||
    marker(raw, '__v_isReadonly') === true
  )
    return undefined
  const innerShallow = shallowExposure(raw, exposure)
  return innerShallow === undefined ? undefined : 5 + Number(shallow) + 2 * Number(innerShallow)
}

// One mode must certify one actual handle for a given storage during the call.
// Distinct handles claiming the same mode are an adapter failure, not new fuel.
export class ExposurePalette extends Detached {
  // Alternating mode/handle pairs per storage; a storage rarely exposes more than one mode.
  declare private readonly exposureOf: (value: object) => ExposureFacet
  declare private readonly known: WeakMap<object, unknown[]>
  declare private readonly storage: (value: object) => object
  constructor(
    exposureOf: (value: object) => ExposureFacet,
    storage: (value: object) => object = storageIdentity,
  ) {
    super()
    this.exposureOf = exposureOf
    this.known = new WeakMap()
    this.storage = storage
  }

  observe(value: object, knownExposure?: ExposureFacet): ExposureObservation | undefined {
    const storage = this.storage(value)
    // An ordinary object is its own storage and its own mode-0 handle, so recording it could
    // never reject a later observation: mode 0 needs no entry.
    if (storage === value) return { mode: 0, storage }
    const mode = classifyExposure(value, storage, knownExposure ?? this.exposureOf(value))
    if (mode === undefined) return undefined
    let modes = this.known.get(storage)
    if (modes === undefined) this.known.set(storage, (modes = []))
    for (let index = 0; index < modes.length; index += 2)
      if (modes[index] === mode) return modes[index + 1] === value ? { mode, storage } : undefined
    modes.push(mode, value)
    return { mode, storage }
  }
}
