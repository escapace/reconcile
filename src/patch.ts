import { isObject, ownKeys } from 'coastal'

import { cloneBufferView } from './clone-buffer-view'
import {
  OBJECT_KIND_ARRAY,
  OBJECT_KIND_ARRAY_BUFFER,
  OBJECT_KIND_DATA_VIEW,
  OBJECT_KIND_DATE,
  OBJECT_KIND_MAP,
  objectKindOf,
  OBJECT_KIND_PLAIN,
  OBJECT_KIND_SET,
  OBJECT_KIND_TYPED_ARRAY,
} from './object-kind'
import { reconcile } from './reconcile'
import { snapshotObjectByKindAfterMiss } from './snapshot'

const PATCH_STATE_SYMBOL = Symbol('@escapace/reconcile/patch')

const UNSUPPORTED_COLLECTION_ITERATION_MESSAGE =
  'Map and Set draft iteration methods are not supported.'

interface PatchContext {
  readonly specialCloneBaseToClone: WeakMap<object, object>
  readonly specialCloneCloneToBase: WeakMap<object, object>
  readonly statesByBase: WeakMap<object, DraftState>
  readonly statesByHandle: WeakMap<object, DraftState>
}

interface BaseDraftState {
  readonly base: object
  readonly context: PatchContext
  copy: object | undefined
  modified: boolean
}

interface ObjectArrayDraftState extends BaseDraftState {
  readonly children: Map<PropertyKey, unknown>
  readonly kind: typeof OBJECT_KIND_ARRAY | typeof OBJECT_KIND_PLAIN
  proxy: object | undefined
}

interface MapDraftState extends BaseDraftState {
  readonly children: Map<unknown, unknown>
  readonly kind: typeof OBJECT_KIND_MAP
  wrapper: DraftMap | undefined
}

interface SetDraftState extends BaseDraftState {
  readonly kind: typeof OBJECT_KIND_SET
  wrapper: DraftSet | undefined
}

type DraftState = MapDraftState | ObjectArrayDraftState | SetDraftState

type DraftableKind =
  | typeof OBJECT_KIND_ARRAY
  | typeof OBJECT_KIND_MAP
  | typeof OBJECT_KIND_PLAIN
  | typeof OBJECT_KIND_SET

function draftValue<T extends object>(state: BaseDraftState): T {
  return (state.copy ?? state.base) as T
}

function prepareObjectArrayCopy(
  state: ObjectArrayDraftState,
): Record<PropertyKey, unknown> | unknown[] {
  if (state.copy !== undefined) {
    return state.copy as Record<PropertyKey, unknown> | unknown[]
  }

  if (state.kind === OBJECT_KIND_ARRAY) {
    state.copy = (state.base as unknown[]).slice()
    return state.copy as unknown[]
  }

  const source = state.base as Record<PropertyKey, unknown>
  const replacement = Object.create(Object.getPrototypeOf(source) as object | null) as Record<
    PropertyKey,
    unknown
  >
  const sourceOwnKeys = ownKeys(source)

  for (let index = 0; index < sourceOwnKeys.length; index += 1) {
    const key = sourceOwnKeys[index]
    const descriptor = Object.getOwnPropertyDescriptor(source, key)

    if (descriptor === undefined) {
      continue
    }

    Object.defineProperty(replacement, key, descriptor)
  }

  state.copy = replacement
  return replacement
}

function prepareMapCopy(state: MapDraftState): Map<unknown, unknown> {
  if (state.copy !== undefined) {
    return state.copy as Map<unknown, unknown>
  }

  state.copy = new Map(state.base as Map<unknown, unknown>)
  return state.copy as Map<unknown, unknown>
}

function prepareSetCopy(state: SetDraftState): Set<unknown> {
  if (state.copy !== undefined) {
    return state.copy as Set<unknown>
  }

  state.copy = new Set(state.base as Set<unknown>)
  return state.copy as Set<unknown>
}

function cloneSpecialValue(
  context: PatchContext,
  value: object,
  kind:
    | typeof OBJECT_KIND_ARRAY_BUFFER
    | typeof OBJECT_KIND_DATA_VIEW
    | typeof OBJECT_KIND_DATE
    | typeof OBJECT_KIND_TYPED_ARRAY,
): object {
  const cached = context.specialCloneBaseToClone.get(value)

  if (cached !== undefined) {
    // Clone-on-read specials must stay stable within one recipe so repeated reads preserve aliasing
    // and shared references collapse to one clone image.
    //
    // Current public call sites usually observe this stability through the surrounding child cache
    // before they would re-enter `cloneSpecialValue(...)`, so this branch mainly preserves helper
    // idempotence if internal call paths broaden later.
    return cached
  }

  const replacement = snapshotObjectByKindAfterMiss(kind, value, context.specialCloneBaseToClone)

  context.specialCloneCloneToBase.set(replacement, value)
  return replacement
}

function materializeChild<K>(
  context: PatchContext,
  children: Map<K, unknown>,
  key: K,
  value: object,
): object {
  const existingState = context.statesByBase.get(value)

  if (existingState !== undefined) {
    const existingDraft =
      existingState.kind === OBJECT_KIND_MAP || existingState.kind === OBJECT_KIND_SET
        ? existingState.wrapper
        : existingState.proxy

    const draft =
      existingDraft ??
      // Reuse the existing state even when its outward proxy or wrapper has not been created yet.
      // That preserves one draft identity per base object across all paths that reach it.
      (existingState.kind === OBJECT_KIND_MAP
        ? ensureDraftMap(existingState)
        : existingState.kind === OBJECT_KIND_SET
          ? ensureDraftSet(existingState)
          : ensureObjectArrayProxy(existingState))

    children.set(key, draft)
    return draft
  }

  const existingClone = context.specialCloneBaseToClone.get(value)

  if (existingClone !== undefined) {
    children.set(key, existingClone)
    return existingClone
  }

  const kind = objectKindOf(value)
  let child: object

  switch (kind) {
    case OBJECT_KIND_ARRAY:
    case OBJECT_KIND_MAP:
    case OBJECT_KIND_PLAIN:
    case OBJECT_KIND_SET:
      child = ensureDraft(context, value, kind)
      break
    case OBJECT_KIND_ARRAY_BUFFER:
    case OBJECT_KIND_DATA_VIEW:
    case OBJECT_KIND_DATE:
    case OBJECT_KIND_TYPED_ARRAY:
      child = cloneSpecialValue(context, value, kind)
      break
    default:
      // Defensive fallback: objectKindOf() currently classifies every object into one of the
      // branches above, but keeping the raw value here avoids surprising breakage if the shared
      // classifier broadens before this call site is updated.
      //
      // The supported public API does not intentionally route values here, so a direct test would
      // be white-box and coupled to internal classifier broadening.
      return value
  }

  children.set(key, child)
  return child
}

type ArrayMutatorName =
  | 'copyWithin'
  | 'fill'
  | 'pop'
  | 'push'
  | 'reverse'
  | 'shift'
  | 'sort'
  | 'splice'
  | 'unshift'

function ensureObjectArrayProxy(state: ObjectArrayDraftState): object {
  if (state.proxy !== undefined) {
    // Repeated ensure calls must reuse the same outward proxy so object identity stays stable
    // within one recipe.
    //
    // Current public call paths usually consult existing outward handles before they would call
    // back into this helper, so this guard is mostly internal idempotence rather than a distinct
    // public behavior target.
    return state.proxy
  }

  const target: object =
    state.kind === OBJECT_KIND_ARRAY
      ? new Array<unknown>()
      : (Object.create(Object.getPrototypeOf(state.base) as object | null) as object)

  const proxy: object = new Proxy(target, {
    deleteProperty(_target, property) {
      const source = draftValue<Record<PropertyKey, unknown> | unknown[]>(state)

      if (!Reflect.has(source, property)) {
        // Deleting a missing property is a true no-op and never marks the draft modified.
        return true
      }

      const copy = prepareObjectArrayCopy(state)
      Reflect.deleteProperty(copy, property)
      state.children.delete(property)
      state.modified = true
      return true
    },
    get(_target, property, receiver) {
      if (state.kind === OBJECT_KIND_ARRAY && typeof property === 'string') {
        switch (property) {
          case 'copyWithin':
          case 'fill':
          case 'pop':
          case 'push':
          case 'reverse':
          case 'shift':
          case 'sort':
          case 'splice':
          case 'unshift': {
            const method = Array.prototype[property as ArrayMutatorName] as (
              ...arguments_: unknown[]
            ) => unknown

            return function (this: unknown, ...arguments_: unknown[]) {
              // Mutating array methods may shift indices, so cached child handles for the old
              // slots are no longer addressable. The inner `set` and `deleteProperty` trap calls
              // flowing through `Reflect.apply` are the source of monotonic `modified` bits.
              state.children.clear()
              return Reflect.apply(method, this, arguments_)
            }
          }
        }
      }

      const childDraft = state.children.get(property)

      if (childDraft !== undefined) {
        return childDraft
      }

      const source = draftValue<Record<PropertyKey, unknown> | unknown[]>(state)
      const hasOwn = Reflect.has(source, property)
      const value: unknown = Reflect.get(source, property, receiver) as unknown

      if (!hasOwn || !isObject(value)) {
        return value
      }

      return materializeChild(state.context, state.children, property, value)
    },
    getOwnPropertyDescriptor(_target, property) {
      const source = draftValue<Record<PropertyKey, unknown> | unknown[]>(state)
      const descriptor = Reflect.getOwnPropertyDescriptor(source, property)

      // Defensive for proxy-backed or otherwise effectful objects whose descriptor lookup can fail
      // for a visible property.
      if (descriptor === undefined) {
        return descriptor
      }

      const childDraft = state.children.get(property)

      if ('value' in descriptor && childDraft !== undefined) {
        descriptor.value = childDraft
        return descriptor
      }

      return descriptor
    },
    getPrototypeOf() {
      return Object.getPrototypeOf(state.base) as object | null
    },
    has(_target, property) {
      return Reflect.has(draftValue<Record<PropertyKey, unknown> | unknown[]>(state), property)
    },
    ownKeys() {
      return Reflect.ownKeys(draftValue<Record<PropertyKey, unknown> | unknown[]>(state))
    },
    set(_target, property, value) {
      const source = draftValue<Record<PropertyKey, unknown> | unknown[]>(state)

      if (Reflect.has(source, property)) {
        const currentValue: unknown = Reflect.get(source, property) as unknown

        if (Object.is(currentValue, value)) {
          // SameValue write against an existing present slot is a no-op. It does not mark the
          // draft modified and it does not clear any cached child handle, so mutations made
          // through that child handle remain sticky.
          return true
        }
      }

      const copy = prepareObjectArrayCopy(state) as Record<PropertyKey, unknown>
      state.children.delete(property)
      copy[property] = value
      state.modified = true
      return true
    },
  })

  state.proxy = proxy
  state.context.statesByHandle.set(proxy, state)
  return proxy
}

function normalizeMapKey(context: PatchContext, key: unknown): unknown {
  if (!isObject(key)) {
    return key
  }

  return context.statesByHandle.get(key)?.base ?? key
}

const LOOKUP_MISS = Symbol('@escapace/reconcile/lookup-not-found')

function resolveSetMember(context: PatchContext, source: Set<unknown>, value: unknown): unknown {
  if (source.has(value)) {
    return value
  }

  if (!isObject(value)) {
    return LOOKUP_MISS
  }

  const draftState = context.statesByHandle.get(value)

  if (draftState !== undefined) {
    const baseValue = draftState.base

    if (source.has(baseValue)) {
      return baseValue
    }

    return LOOKUP_MISS
  }

  const baseState = context.statesByBase.get(value)

  if (baseState !== undefined) {
    const handle =
      baseState.kind === OBJECT_KIND_MAP || baseState.kind === OBJECT_KIND_SET
        ? baseState.wrapper
        : baseState.proxy

    if (handle !== undefined && source.has(handle)) {
      return handle
    }
  }

  return LOOKUP_MISS
}

class DraftMap {
  readonly [PATCH_STATE_SYMBOL]: MapDraftState

  constructor(state: MapDraftState) {
    this[PATCH_STATE_SYMBOL] = state
  }

  get size(): number {
    const state = this[PATCH_STATE_SYMBOL]
    return draftValue<Map<unknown, unknown>>(state).size
  }

  clear(): void {
    const state = this[PATCH_STATE_SYMBOL]
    const source = draftValue<Map<unknown, unknown>>(state)

    if (source.size === 0) {
      // Clearing an already-empty map is a true no-op and does not mark the draft modified.
      return
    }

    prepareMapCopy(state).clear()
    state.children.clear()
    state.modified = true
  }

  delete(key: unknown): boolean {
    const state = this[PATCH_STATE_SYMBOL]
    const source = draftValue<Map<unknown, unknown>>(state)
    const normalizedKey = normalizeMapKey(state.context, key)

    if (!source.has(normalizedKey)) {
      // Deleting a missing key is a true no-op and does not mark the draft modified.
      return false
    }

    prepareMapCopy(state).delete(normalizedKey)
    state.children.delete(normalizedKey)
    state.modified = true
    return true
  }

  entries(): never {
    throw new TypeError(UNSUPPORTED_COLLECTION_ITERATION_MESSAGE)
  }

  forEach(): never {
    throw new TypeError(UNSUPPORTED_COLLECTION_ITERATION_MESSAGE)
  }

  get(key: unknown): unknown {
    const state = this[PATCH_STATE_SYMBOL]
    const source = draftValue<Map<unknown, unknown>>(state)
    const normalizedKey = normalizeMapKey(state.context, key)
    const childDraft = state.children.get(normalizedKey)

    if (childDraft !== undefined) {
      return childDraft
    }

    const value = source.get(normalizedKey)

    if (value === undefined && !source.has(normalizedKey)) {
      return undefined
    }

    if (!isObject(value)) {
      return value
    }

    return materializeChild(state.context, state.children, normalizedKey, value)
  }

  has(key: unknown): boolean {
    const state = this[PATCH_STATE_SYMBOL]
    return draftValue<Map<unknown, unknown>>(state).has(normalizeMapKey(state.context, key))
  }

  keys(): never {
    throw new TypeError(UNSUPPORTED_COLLECTION_ITERATION_MESSAGE)
  }

  set(key: unknown, value: unknown): this {
    const state = this[PATCH_STATE_SYMBOL]
    const normalizedKey = normalizeMapKey(state.context, key)
    const source = draftValue<Map<unknown, unknown>>(state)
    const currentValue = source.get(normalizedKey)

    if (
      Object.is(currentValue, value) &&
      (currentValue !== undefined || source.has(normalizedKey))
    ) {
      // SameValue write against an existing present entry is a no-op. It does not mark the draft
      // modified and leaves cached child handles for that key in place.
      return this
    }

    const copy = prepareMapCopy(state)
    state.children.delete(normalizedKey)
    copy.set(normalizedKey, value)
    state.modified = true
    return this
  }

  values(): never {
    throw new TypeError(UNSUPPORTED_COLLECTION_ITERATION_MESSAGE)
  }

  [Symbol.iterator](): never {
    throw new TypeError(UNSUPPORTED_COLLECTION_ITERATION_MESSAGE)
  }
}

function ensureDraftMap(state: MapDraftState): DraftMap {
  if (state.wrapper !== undefined) {
    // Repeated ensure calls must reuse the same outward wrapper so one base map corresponds to
    // one draft-facing identity.
    //
    // Current public call paths usually observe this through earlier existing-handle checks, so
    // this branch mainly keeps the helper idempotent for internal reuse.
    return state.wrapper
  }

  const wrapper = new DraftMap(state)
  state.wrapper = wrapper
  state.context.statesByHandle.set(wrapper, state)
  return wrapper
}

class DraftSet {
  readonly [PATCH_STATE_SYMBOL]: SetDraftState

  constructor(state: SetDraftState) {
    this[PATCH_STATE_SYMBOL] = state
  }

  get size(): number {
    const state = this[PATCH_STATE_SYMBOL]
    return draftValue<Set<unknown>>(state).size
  }

  add(value: unknown): this {
    const state = this[PATCH_STATE_SYMBOL]
    const source = draftValue<Set<unknown>>(state)

    if (resolveSetMember(state.context, source, value) !== LOOKUP_MISS) {
      // Duplicate add is a true no-op and does not mark the draft modified.
      return this
    }

    prepareSetCopy(state).add(value)
    state.modified = true
    return this
  }

  clear(): void {
    const state = this[PATCH_STATE_SYMBOL]
    const source = draftValue<Set<unknown>>(state)

    if (source.size === 0) {
      // Clearing an already-empty set is a true no-op and does not mark the draft modified.
      return
    }

    prepareSetCopy(state).clear()
    state.modified = true
  }

  delete(value: unknown): boolean {
    const state = this[PATCH_STATE_SYMBOL]
    const source = draftValue<Set<unknown>>(state)
    const target = resolveSetMember(state.context, source, value)

    if (target === LOOKUP_MISS) {
      // Deleting a missing element is a true no-op and does not mark the draft modified.
      return false
    }

    const removed = prepareSetCopy(state).delete(target)
    if (removed) {
      state.modified = true
    }
    return removed
  }

  entries(): never {
    throw new TypeError(UNSUPPORTED_COLLECTION_ITERATION_MESSAGE)
  }

  forEach(): never {
    throw new TypeError(UNSUPPORTED_COLLECTION_ITERATION_MESSAGE)
  }

  has(value: unknown): boolean {
    const state = this[PATCH_STATE_SYMBOL]
    const source = draftValue<Set<unknown>>(state)
    return resolveSetMember(state.context, source, value) !== LOOKUP_MISS
  }

  keys(): never {
    throw new TypeError(UNSUPPORTED_COLLECTION_ITERATION_MESSAGE)
  }

  values(): never {
    throw new TypeError(UNSUPPORTED_COLLECTION_ITERATION_MESSAGE)
  }

  [Symbol.iterator](): never {
    throw new TypeError(UNSUPPORTED_COLLECTION_ITERATION_MESSAGE)
  }
}

function ensureDraftSet(state: SetDraftState): DraftSet {
  if (state.wrapper !== undefined) {
    // Repeated ensure calls must reuse the same outward wrapper so one base set corresponds to
    // one draft-facing identity.
    //
    // Current public call paths usually observe this through earlier existing-handle checks, so
    // this branch mainly keeps the helper idempotent for internal reuse.
    return state.wrapper
  }

  const wrapper = new DraftSet(state)
  state.wrapper = wrapper
  state.context.statesByHandle.set(wrapper, state)
  return wrapper
}

function ensureDraft(
  context: PatchContext,
  value: object,
  knownKind: DraftableKind | undefined = undefined,
): object {
  const existing = context.statesByBase.get(value)

  if (existing !== undefined) {
    // Re-ensuring an already tracked base must reuse its existing draft state and outward handle
    // instead of allocating a second state for the same object.
    //
    // `materializeChild(...)` short-circuits most public repeated reaches before they would call
    // back into `ensureDraft(...)`, so this branch is primarily an internal coherence guard.
    switch (existing.kind) {
      case OBJECT_KIND_MAP:
        return ensureDraftMap(existing)
      case OBJECT_KIND_SET:
        return ensureDraftSet(existing)
      default:
        return ensureObjectArrayProxy(existing)
    }
  }

  const kind = knownKind ?? objectKindOf(value)

  switch (kind) {
    case OBJECT_KIND_ARRAY:
    case OBJECT_KIND_PLAIN: {
      const state: ObjectArrayDraftState = {
        base: value,
        children: new Map<PropertyKey, unknown>(),
        context,
        copy: undefined,
        kind,
        modified: false,
        proxy: undefined,
      }
      context.statesByBase.set(value, state)
      return ensureObjectArrayProxy(state)
    }
    case OBJECT_KIND_MAP: {
      const state: MapDraftState = {
        base: value,
        children: new Map<unknown, unknown>(),
        context,
        copy: undefined,
        kind,
        modified: false,
        wrapper: undefined,
      }
      context.statesByBase.set(value, state)
      return ensureDraftMap(state)
    }
    case OBJECT_KIND_SET: {
      const state: SetDraftState = {
        base: value,
        context,
        copy: undefined,
        kind,
        modified: false,
        wrapper: undefined,
      }
      context.statesByBase.set(value, state)
      return ensureDraftSet(state)
    }
    default:
      // Defensive fallback for future classifier broadening or accidental internal misuse. Current
      // supported call sites do not intentionally route unmatched kinds through ensureDraft().
      //
      // The public API is expected to reach special values through dedicated branches before this
      // point, so testing this directly would require white-box coupling to internal dispatch.
      return cloneSpecialValue(context, value, kind)
  }
}

function isSpecialValueEquivalent(base: object, candidate: object): boolean {
  switch (objectKindOf(base)) {
    case OBJECT_KIND_ARRAY_BUFFER: {
      const left = base as ArrayBuffer
      const right = candidate as ArrayBuffer

      // Length mismatch is a real semantic change: clone-on-read buffers must not collapse back to
      // the base reference when the byte extent changed.
      //
      // Public clone-on-read buffers are created as fixed-length snapshots, so current supported
      // recipes do not have a clean way to reach this mismatch. The check stays as a defensive
      // coherence guard if future internals admit broader buffer inputs here.
      if (left.byteLength !== right.byteLength) {
        return false
      }

      const leftBytes = new Uint8Array(left)
      const rightBytes = new Uint8Array(right)

      for (let index = 0; index < leftBytes.length; index += 1) {
        if (leftBytes[index] !== rightBytes[index]) {
          return false
        }
      }

      return true
    }
    case OBJECT_KIND_DATA_VIEW:
    case OBJECT_KIND_TYPED_ARRAY: {
      const left = base as ArrayBufferView
      const right = candidate as ArrayBufferView

      // Constructor, offset, and length are part of the observable view identity. A mismatch means
      // the candidate view is semantically changed even if the underlying bytes still line up.
      //
      // Public clone-on-read views keep fixed constructor, offset, and byte length once cloned, so
      // current supported recipes do not have a clean way to reach this mismatch. The check stays
      // as a defensive coherence guard if broader internal inputs ever flow through this helper.
      if (
        left.constructor !== right.constructor ||
        left.byteOffset !== right.byteOffset ||
        left.byteLength !== right.byteLength
      ) {
        return false
      }

      const leftBytes = new Uint8Array(left.buffer, left.byteOffset, left.byteLength)
      const rightBytes = new Uint8Array(right.buffer, right.byteOffset, right.byteLength)

      for (let index = 0; index < leftBytes.length; index += 1) {
        if (leftBytes[index] !== rightBytes[index]) {
          return false
        }
      }

      return true
    }
    case OBJECT_KIND_DATE:
      return (base as Date).getTime() === (candidate as Date).getTime()
    default:
      // Defensive fallback: callers currently use this helper for clone-on-read specials, but the
      // generic SameValue path keeps the helper safe if that discipline broadens later.
      // No supported public recipe currently routes non-special values here.
      return Object.is(base, candidate)
  }
}

// Under the monotonic write model, object, array, map, and set drafts use a sticky `modified`
// bit as the primary unchanged predicate: the first real mutation permanently marks the draft
// modified for the rest of the recipe, and no later write collapses it back to unmodified.
//
// A draft that is itself unmodified can still need finalization when a descendant reached
// through its base graph is modified or clone-on-read, for example a shared object touched only
// through a sibling path or a `Date` read-through. `needsMaterialization(...)` recursively walks
// the base graph and answers that question coherently, and `materializeState(...)` delegates to
// it for unmodified draft states so the shared-descendant case still finalizes correctly.
//
// Clone-on-read specials (`Date`, `ArrayBuffer`, `DataView`, typed arrays) stay on the existing
// semantic-equivalence policy and are unified into the same materialization pipeline through
// `isSpecialValueEquivalent(...)` at finalization time, because they mutate outside the proxy
// write path and cannot be tracked by the monotonic draft `modified` bit.
function needsMaterialization(
  context: PatchContext,
  value: unknown,
  memo: WeakMap<object, boolean>,
): boolean {
  if (!isObject(value)) {
    return false
  }

  const cached = memo.get(value)

  if (cached !== undefined) {
    return cached
  }

  const draftState = context.statesByHandle.get(value) ?? context.statesByBase.get(value)

  // Clone-on-read specials always require finalization whenever they are tracked. Their
  // unchanged-vs-changed decision is made by `isSpecialValueEquivalent(...)` later in the
  // materialize pipeline.
  if (
    draftState === undefined &&
    (context.specialCloneCloneToBase.get(value) !== undefined ||
      context.specialCloneBaseToClone.get(value) !== undefined)
  ) {
    memo.set(value, true)
    return true
  }

  if (draftState !== undefined) {
    if (draftState.modified) {
      memo.set(value, true)
      return true
    }

    // An unmodified managed draft can still need materialization if any descendant reached
    // through its base graph is modified or clone-on-read. Walk the base to answer that.
    const base = draftState.base
    const baseCached = memo.get(base)

    if (baseCached !== undefined) {
      if (base !== value) {
        memo.set(value, baseCached)
      }
      return baseCached
    }

    // Speculate no before recursing so cyclic base graphs terminate cleanly.
    memo.set(value, false)
    if (base !== value) {
      memo.set(base, false)
    }

    const descendantResult = walkDescendantsForMaterialization(context, base, memo)

    if (descendantResult) {
      memo.set(value, true)
      if (base !== value) {
        memo.set(base, true)
      }
    }

    return descendantResult
  }

  // Speculate no before recursing so cyclic graphs terminate cleanly.
  memo.set(value, false)

  const result = walkDescendantsForMaterialization(context, value, memo)

  if (result) {
    memo.set(value, true)
  }

  return result
}

function walkDescendantsForMaterialization(
  context: PatchContext,
  value: object,
  memo: WeakMap<object, boolean>,
): boolean {
  switch (objectKindOf(value)) {
    case OBJECT_KIND_ARRAY: {
      const arrayValue = value as unknown[]

      for (let index = 0; index < arrayValue.length; index += 1) {
        if (!(index in arrayValue)) {
          continue
        }

        if (needsMaterialization(context, arrayValue[index], memo)) {
          return true
        }
      }

      return false
    }
    case OBJECT_KIND_MAP:
      for (const [key, entry] of value as Map<unknown, unknown>) {
        if (
          needsMaterialization(context, key, memo) ||
          needsMaterialization(context, entry, memo)
        ) {
          return true
        }
      }

      return false
    case OBJECT_KIND_PLAIN: {
      const objectValue = value as Record<PropertyKey, unknown>
      const objectOwnKeys = ownKeys(value)

      for (let index = 0; index < objectOwnKeys.length; index += 1) {
        if (needsMaterialization(context, objectValue[objectOwnKeys[index]], memo)) {
          return true
        }
      }

      return false
    }
    case OBJECT_KIND_SET:
      for (const entry of value as Set<unknown>) {
        if (needsMaterialization(context, entry, memo)) {
          return true
        }
      }

      return false
    default:
      return false
  }
}

function materializePlainObject(
  context: PatchContext,
  source: Record<PropertyKey, unknown>,
  state: ObjectArrayDraftState | undefined,
  memo: WeakMap<object, unknown>,
  requiresMemo: WeakMap<object, boolean>,
  memoKey: object,
): Record<PropertyKey, unknown> {
  const replacement = Object.create(Object.getPrototypeOf(source) as object | null) as Record<
    PropertyKey,
    unknown
  >
  memo.set(memoKey, replacement)

  const sourceOwnKeys = ownKeys(source)
  const children = state?.children

  for (let index = 0; index < sourceOwnKeys.length; index += 1) {
    const key = sourceOwnKeys[index]
    const descriptor = Object.getOwnPropertyDescriptor(source, key)
    const childDraft = children?.get(key)

    if (descriptor !== undefined && 'value' in descriptor) {
      descriptor.value = materializeValue(
        context,
        childDraft ?? descriptor.value,
        memo,
        requiresMemo,
      )
      Object.defineProperty(replacement, key, descriptor)
      continue
    }

    replacement[key] = materializeValue(context, childDraft ?? source[key], memo, requiresMemo)
  }

  return replacement
}

function materializeArray(
  context: PatchContext,
  source: unknown[],
  state: ObjectArrayDraftState | undefined,
  memo: WeakMap<object, unknown>,
  requiresMemo: WeakMap<object, boolean>,
  memoKey: object,
): unknown[] {
  const replacement = new Array<unknown>(source.length)
  memo.set(memoKey, replacement)
  const children = state?.children

  for (let index = 0; index < source.length; index += 1) {
    if (!(index in source)) {
      continue
    }

    const childKey = String(index)
    const childDraft = children?.get(childKey)
    replacement[index] = materializeValue(context, childDraft ?? source[index], memo, requiresMemo)
  }

  return replacement
}

function materializeMap(
  context: PatchContext,
  source: Map<unknown, unknown>,
  state: MapDraftState | undefined,
  memo: WeakMap<object, unknown>,
  requiresMemo: WeakMap<object, boolean>,
  memoKey: object,
): Map<unknown, unknown> {
  const replacement = new Map<unknown, unknown>()
  memo.set(memoKey, replacement)
  const children = state?.children

  for (const [key, value] of source) {
    const finalizedKey = isObject(key) ? materializeValue(context, key, memo, requiresMemo) : key

    const childDraft = children?.get(key)
    const finalizedValue = materializeValue(context, childDraft ?? value, memo, requiresMemo)

    replacement.set(finalizedKey, finalizedValue)
  }

  return replacement
}

function materializeSet(
  context: PatchContext,
  source: Set<unknown>,
  memo: WeakMap<object, unknown>,
  requiresMemo: WeakMap<object, boolean>,
  memoKey: object,
): Set<unknown> {
  const replacement = new Set<unknown>()
  memo.set(memoKey, replacement)

  for (const entry of source) {
    replacement.add(materializeValue(context, entry, memo, requiresMemo))
  }

  return replacement
}

function materializeState(
  context: PatchContext,
  state: DraftState,
  memo: WeakMap<object, unknown>,
  requiresMemo: WeakMap<object, boolean>,
): object {
  const cached = memo.get(state.base)

  if (cached !== undefined) {
    return cached as object
  }

  // Monotonic model: a draft that is itself unmodified reuses base as-is unless a descendant
  // reached through its base graph forces materialization (shared draft touched via a sibling,
  // clone-on-read special, etc.). `needsMaterialization(...)` centralizes that recursive check.
  if (!state.modified && !needsMaterialization(context, state.base, requiresMemo)) {
    memo.set(state.base, state.base)
    return state.base
  }

  const source = draftValue(state)

  switch (state.kind) {
    case OBJECT_KIND_ARRAY:
      return materializeArray(context, source as unknown[], state, memo, requiresMemo, state.base)
    case OBJECT_KIND_MAP:
      return materializeMap(
        context,
        source as Map<unknown, unknown>,
        state,
        memo,
        requiresMemo,
        state.base,
      )
    case OBJECT_KIND_PLAIN:
      return materializePlainObject(
        context,
        source as Record<PropertyKey, unknown>,
        state,
        memo,
        requiresMemo,
        state.base,
      )
    case OBJECT_KIND_SET:
      return materializeSet(context, source as Set<unknown>, memo, requiresMemo, state.base)
  }
}

function materializeValue(
  context: PatchContext,
  value: unknown,
  memo: WeakMap<object, unknown>,
  requiresMemo: WeakMap<object, boolean>,
): unknown {
  if (!isObject(value)) {
    return value
  }

  const cached = memo.get(value)

  if (cached !== undefined) {
    return cached
  }

  const draftState = context.statesByHandle.get(value) ?? context.statesByBase.get(value)

  if (draftState !== undefined) {
    return materializeState(context, draftState, memo, requiresMemo)
  }

  const specialCloneBase = context.specialCloneCloneToBase.get(value)

  if (specialCloneBase !== undefined) {
    const finalized = isSpecialValueEquivalent(specialCloneBase, value) ? specialCloneBase : value

    memo.set(value, finalized)
    return finalized
  }

  const mappedClone = context.specialCloneBaseToClone.get(value)

  if (mappedClone !== undefined) {
    memo.set(value, mappedClone)
    return mappedClone
  }

  const kind = objectKindOf(value)

  switch (kind) {
    case OBJECT_KIND_ARRAY_BUFFER: {
      const replacement = (value as ArrayBuffer).slice(0)
      memo.set(value, replacement)
      return replacement
    }
    case OBJECT_KIND_DATA_VIEW:
    case OBJECT_KIND_TYPED_ARRAY: {
      const sourceView = value as ArrayBufferView
      const replacement = cloneBufferView(
        sourceView,
        materializeValue(context, sourceView.buffer, memo, requiresMemo) as ArrayBuffer,
      )
      memo.set(value, replacement)
      return replacement
    }
    case OBJECT_KIND_DATE: {
      const replacement = new Date((value as Date).getTime())
      memo.set(value, replacement)
      return replacement
    }
    case OBJECT_KIND_ARRAY:
    case OBJECT_KIND_MAP:
    case OBJECT_KIND_PLAIN:
    case OBJECT_KIND_SET:
      if (!needsMaterialization(context, value, requiresMemo)) {
        memo.set(value, value)
        return value
      }

      switch (kind) {
        case OBJECT_KIND_ARRAY:
          return materializeArray(context, value as unknown[], undefined, memo, requiresMemo, value)
        case OBJECT_KIND_MAP:
          return materializeMap(
            context,
            value as Map<unknown, unknown>,
            undefined,
            memo,
            requiresMemo,
            value,
          )
        case OBJECT_KIND_PLAIN:
          return materializePlainObject(
            context,
            value as Record<PropertyKey, unknown>,
            undefined,
            memo,
            requiresMemo,
            value,
          )
        case OBJECT_KIND_SET:
          return materializeSet(context, value as Set<unknown>, memo, requiresMemo, value)
      }
  }
}

/**
 * Runs `recipe` against a temporary writable draft of `current` and returns the resulting next value without applying it back onto `current`.
 *
 * @remarks
 * `createPatch(...)` is the draft-building half of `patch(...)`. It gives `recipe` a temporary
 * draft that can be mutated like ordinary JavaScript data, then returns the next value produced by
 * that recipe. The recipe may return the draft root, a nested draft value, or any replacement
 * value. Draft values created by this call are turned back into ordinary JavaScript values before
 * return. If a replacement value contains nested draft values created by this call, those nested
 * draft values are also turned back into ordinary JavaScript values before return. A non-draft
 * return wins over draft mutations. Returning `current` by reference discards draft mutations and
 * returns the original value.
 *
 * Supported values match `snapshot(...)` and `reconcile(current, next)`. Plain objects, arrays,
 * `Map`,
 * and `Set` are drafted structurally. `Set` drafts keep normal set membership behavior within one
 * recipe. When the recipe reads a `Date`, `ArrayBuffer`, `DataView`, or typed array, it sees a
 * writable copy rather than a partially wrapped live value. If that copy is left unchanged, the
 * result reuses the original `Date`, buffer, or view references. If it is changed, the result
 * contains changed copies and preserves `ArrayBuffer` or view aliasing. Primitive values and
 * functions are treated as single values. Other object types, including many class instances or
 * prototype-bearing values, are handled on a best-effort basis rather than rejected up front.
 *
 * For plain objects, arrays, `Map`, and `Set`, reads do not mark changes, and writing the same
 * value back does not count as a change. Once a real change happens on one draft node, later
 * writes do not restore that node to the original reference, even if the final contents match
 * `current` again.
 *
 * The returned value is not frozen and it is not guaranteed to be detached from `current`.
 * Untouched subtrees may stay shared. Supported results preserve plain-object key order,
 * sparse-array holes, cycles, shared references, and `ArrayBuffer` or view aliasing. The same
 * behavior also applies to common reactive or signal-backed wrappers when they expose object,
 * array, map, or set behavior.
 *
 * Array drafts support normal array iteration, including `for...of`, `entries()`, `keys()`,
 * `values()`, and callback-style array methods. `Map` and `Set` draft `keys()`, `values()`,
 * `entries()`, `[Symbol.iterator]()`, and `forEach()` are out of scope and throw when called.
 *
 * `createPatch(...)` is appropriate when a next value is needed without applying it back onto the
 * existing value. `snapshot(createPatch(...))` produces a detached copy. `patch(...)` applies the
 * result through `reconcile(current, next)`.
 *
 * @param current - Existing value.
 * @param recipe - Receives a temporary writable draft of `current` and computes the next value.
 * @returns The next value produced by the recipe.
 * @throws When the recipe calls out-of-scope `Map` or `Set` draft iterator or callback APIs.
 */
export function createPatch<T, R>(current: T, recipe: (draft: T) => R): R {
  const context: PatchContext = {
    specialCloneBaseToClone: new WeakMap<object, object>(),
    specialCloneCloneToBase: new WeakMap<object, object>(),
    statesByBase: new WeakMap<object, DraftState>(),
    statesByHandle: new WeakMap<object, DraftState>(),
  }
  let draft = current

  if (isObject(current)) {
    const kind = objectKindOf(current)

    switch (kind) {
      case OBJECT_KIND_ARRAY:
      case OBJECT_KIND_MAP:
      case OBJECT_KIND_PLAIN:
      case OBJECT_KIND_SET:
        draft = ensureDraft(context, current, kind) as T
        break
      default:
        draft = cloneSpecialValue(context, current, kind) as T
    }
  }

  const result = recipe(draft)

  // If the recipe explicitly returns the original current value (same identity),
  // honor that intent and return it without finalization. This allows users to
  // "cancel" all draft mutations by returning the original.
  if ((result as unknown) === current) {
    return result
  }

  if (!isObject(result)) {
    return result
  }

  const requiresMemo = new WeakMap<object, boolean>()

  if (!needsMaterialization(context, result, requiresMemo)) {
    // When the recipe returns a draft handle whose state is unmodified and whose descendants do
    // not need materialization, the handle must be unwrapped to its backing base before return.
    // Returning the handle would leak the proxy or collection wrapper to the caller.
    const handleState = context.statesByHandle.get(result)

    if (handleState !== undefined) {
      return handleState.base as R
    }

    return result
  }

  return materializeValue(context, result, new WeakMap<object, unknown>(), requiresMemo) as R
}

/**
 * Runs `recipe` against a temporary writable draft of `current`, then applies the resulting next value back onto `current` through `reconcile(...)`.
 *
 * @remarks
 * `patch(...)` is the convenience wrapper around `createPatch(...)` and `reconcile(current, next)`. It is
 * equivalent to `reconcile(current, createPatch(current, recipe))`. The same recipe return rules as
 * `createPatch(...)` apply: the recipe may return the draft root, a nested draft value, or any
 * replacement value. If a replacement value contains nested draft values created by this call,
 * those nested draft values are turned back into ordinary JavaScript values before publication. A
 * non-draft return wins over draft mutations. Returning `current` by reference discards draft
 * mutations and returns the original value.
 *
 * Supported values, draft behavior, and exclusions match `createPatch(...)`. Plain objects,
 * arrays, `Map`, and `Set` are drafted structurally. `Date`, `ArrayBuffer`, `DataView`, and typed
 * arrays use the same copy-on-read behavior. Other object types, including many class instances or
 * prototype-bearing values, are handled on a best-effort basis rather than rejected up front. The
 * same behavior also applies to common reactive or signal-backed wrappers when they expose object,
 * array, map, or set behavior. Array drafts support normal array iteration, including `for...of`,
 * `entries()`, `keys()`, `values()`, and callback-style array methods. `Map` and `Set` draft
 * `keys()`, `values()`, `entries()`, `[Symbol.iterator]()`, and `forEach()` are out of scope and
 * throw when called.
 *
 * After the recipe finishes, `patch(...)` applies the next value through `reconcile(current, next)`. That
 * means existing objects and collections may be kept when they can be updated in place. The result
 * preserves plain-object key order, sparse-array holes, cycles, shared references, and
 * `ArrayBuffer` or view aliasing. Because the next value is applied through `reconcile(current, next)`,
 * `patch(...)` may return `current` even when `createPatch(...)` would return a fresh but
 * equivalent next value.
 *
 * `createPatch(...)` is appropriate when a next value is needed without applying it back onto the
 * existing value. `snapshot(createPatch(...))` produces a detached copy.
 *
 * @param current - Existing value.
 * @param recipe - Receives a temporary writable draft of `current` and computes the next value.
 * @returns The value after the recipe result has been applied through `reconcile(current, next)`.
 * @throws When the recipe calls out-of-scope `Map` or `Set` draft iterator or callback APIs.
 */
export function patch<T, R>(current: T, recipe: (draft: T) => R): R {
  return reconcile(current, createPatch(current, recipe))
}
