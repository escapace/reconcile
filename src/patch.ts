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
import type { ObjectKind } from './object-kind'
import { reconcile } from './reconcile'
import { snapshotObjectByKindAfterMiss } from './snapshot'

const PATCH_STATE_SYMBOL = Symbol('@escapace/reconcile/patch')

const UNSUPPORTED_COLLECTION_ITERATION_MESSAGE =
  'Map and Set draft iteration methods are not supported.'

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

function draftHandleOf(state: DraftState): object | undefined {
  switch (state.kind) {
    case OBJECT_KIND_MAP:
    case OBJECT_KIND_SET:
      return state.wrapper
    default:
      return state.proxy
  }
}

function ensureObjectArrayProxy(state: ObjectArrayDraftState): object {
  const target: object =
    state.kind === OBJECT_KIND_ARRAY
      ? new Array<unknown>()
      : (Object.create(Object.getPrototypeOf(state.base) as object | null) as object)

  const proxy: object = new Proxy(target, {
    deleteProperty(_target, property) {
      const source = draftValue<Record<PropertyKey, unknown> | unknown[]>(state)

      if (!Object.prototype.hasOwnProperty.call(source, property)) {
        // Deletion cannot remove inherited properties, so only own properties mark a change.
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
            // eslint-disable-next-line typescript/unbound-method
            const method = Array.prototype[property] as (...arguments_: unknown[]) => unknown

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

      return state.context.materializeChild(state.children, property, value)
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

      // An inherited equal value still needs an own property created by this write.
      if (Object.prototype.hasOwnProperty.call(source, property)) {
        const currentValue: unknown = Reflect.get(source, property) as unknown

        if (state.context.isSameDraftValue(currentValue, value)) {
          // SameValue write against an existing present slot is a no-op. It does not mark the
          // draft modified and it does not clear any cached child handle, so mutations made
          // through that child handle remain sticky.
          return true
        }
      }

      const copy = prepareObjectArrayCopy(state) as Record<PropertyKey, unknown>
      state.children.delete(property)
      copy[property] = value
      if (state.kind === OBJECT_KIND_ARRAY && property === 'length') {
        // A length write deletes indices without invoking this proxy's delete trap.
        for (const key of state.children.keys()) {
          if (!Object.prototype.hasOwnProperty.call(copy, key)) {
            state.children.delete(key)
          }
        }
      }
      state.modified = true
      return true
    },
  })

  state.proxy = proxy
  state.context.statesByHandle.set(proxy, state)
  return proxy
}

const LOOKUP_MISS = Symbol('@escapace/reconcile/lookup-not-found')

function throwUnsupportedCollectionIteration(): never {
  throw new TypeError(UNSUPPORTED_COLLECTION_ITERATION_MESSAGE)
}

abstract class UnsupportedDraftCollectionIteration {
  entries(): never {
    return throwUnsupportedCollectionIteration()
  }

  forEach(): never {
    return throwUnsupportedCollectionIteration()
  }

  keys(): never {
    return throwUnsupportedCollectionIteration()
  }

  values(): never {
    return throwUnsupportedCollectionIteration()
  }

  [Symbol.iterator](): never {
    return throwUnsupportedCollectionIteration()
  }
}

class DraftMap extends UnsupportedDraftCollectionIteration {
  readonly [PATCH_STATE_SYMBOL]: MapDraftState

  constructor(state: MapDraftState) {
    super()
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
    const normalizedKey = state.context.resolveMapKey(source, key)

    if (!source.has(normalizedKey)) {
      // Deleting a missing key is a true no-op and does not mark the draft modified.
      return false
    }

    prepareMapCopy(state).delete(normalizedKey)
    state.children.delete(normalizedKey)
    state.modified = true
    return true
  }

  get(key: unknown): unknown {
    const state = this[PATCH_STATE_SYMBOL]
    const source = draftValue<Map<unknown, unknown>>(state)
    const normalizedKey = state.context.resolveMapKey(source, key)
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

    return state.context.materializeChild(state.children, normalizedKey, value)
  }

  has(key: unknown): boolean {
    const state = this[PATCH_STATE_SYMBOL]
    const source = draftValue<Map<unknown, unknown>>(state)
    return source.has(state.context.resolveMapKey(source, key))
  }

  set(key: unknown, value: unknown): this {
    const state = this[PATCH_STATE_SYMBOL]
    const source = draftValue<Map<unknown, unknown>>(state)
    const normalizedKey = state.context.resolveMapKey(source, key)
    const currentValue = source.get(normalizedKey)

    if (
      state.context.isSameDraftValue(currentValue, value) &&
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
}

function ensureDraftMap(state: MapDraftState): DraftMap {
  const wrapper = new DraftMap(state)
  state.wrapper = wrapper
  state.context.statesByHandle.set(wrapper, state)
  return wrapper
}

class DraftSet extends UnsupportedDraftCollectionIteration {
  readonly [PATCH_STATE_SYMBOL]: SetDraftState

  constructor(state: SetDraftState) {
    super()
    this[PATCH_STATE_SYMBOL] = state
  }

  get size(): number {
    const state = this[PATCH_STATE_SYMBOL]
    return draftValue<Set<unknown>>(state).size
  }

  add(value: unknown): this {
    const state = this[PATCH_STATE_SYMBOL]
    const source = draftValue<Set<unknown>>(state)

    if (state.context.resolveSetMember(source, value) !== LOOKUP_MISS) {
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
    const target = state.context.resolveSetMember(source, value)

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

  has(value: unknown): boolean {
    const state = this[PATCH_STATE_SYMBOL]
    const source = draftValue<Set<unknown>>(state)
    return state.context.resolveSetMember(source, value) !== LOOKUP_MISS
  }
}

function ensureDraftSet(state: SetDraftState): DraftSet {
  const wrapper = new DraftSet(state)
  state.wrapper = wrapper
  state.context.statesByHandle.set(wrapper, state)
  return wrapper
}

type CloneOnReadKind =
  | typeof OBJECT_KIND_ARRAY_BUFFER
  | typeof OBJECT_KIND_DATA_VIEW
  | typeof OBJECT_KIND_DATE
  | typeof OBJECT_KIND_TYPED_ARRAY

function cloneOnReadSpecialKind(kind: ObjectKind): CloneOnReadKind | undefined {
  return kind === OBJECT_KIND_ARRAY_BUFFER ||
    kind === OBJECT_KIND_DATA_VIEW ||
    kind === OBJECT_KIND_DATE ||
    kind === OBJECT_KIND_TYPED_ARRAY
    ? kind
    : undefined
}

function isSpecialValueEquivalent(
  base: object,
  candidate: object,
  knownKind: CloneOnReadKind = cloneOnReadSpecialKind(objectKindOf(base))!,
): boolean {
  switch (knownKind) {
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

      const leftBuffer = left.buffer
      const rightBuffer = right.buffer

      if (leftBuffer.byteLength !== rightBuffer.byteLength) {
        return false
      }

      const leftBufferBytes = new Uint8Array(leftBuffer)
      const rightBufferBytes = new Uint8Array(rightBuffer)

      for (let index = 0; index < leftBufferBytes.length; index += 1) {
        if (leftBufferBytes[index] !== rightBufferBytes[index]) {
          return false
        }
      }

      return true
    }
    case OBJECT_KIND_DATE:
      return Object.is((base as Date).getTime(), (candidate as Date).getTime())
    default:
      // Defensive fallback: callers currently use this helper for clone-on-read specials, but the
      // generic SameValue path keeps the helper safe if that discipline broadens later.
      // No supported public recipe currently routes non-special values here.
      return Object.is(base, candidate)
  }
}

interface MaterializationPlan {
  clonesSpecialValues: boolean
  readonly deferred: Map<object, () => unknown>
  parent: object | undefined
  readonly parents: WeakMap<object, Set<object>>
  readonly pending: object[]
  readonly required: WeakSet<object>
}

class PatchContext {
  private materializationPlan: MaterializationPlan | undefined
  private materializationRequired: WeakMap<object, boolean> | undefined
  private materializationVisited: Set<object> | undefined
  private materializedValues: WeakMap<object, unknown> | undefined
  readonly specialCloneBaseToClone = new WeakMap<object, object>()
  readonly specialCloneCloneToBase = new WeakMap<object, object>()
  readonly statesByBase = new WeakMap<object, DraftState>()
  readonly statesByHandle = new WeakMap<object, DraftState>()
  private readonly untrackedSpecialsToClone = new WeakSet<object>()

  private getMaterializationRequired(): WeakMap<object, boolean> {
    this.materializationRequired ??= new WeakMap<object, boolean>()

    return this.materializationRequired
  }

  private getMaterializedValues(): WeakMap<object, unknown> {
    this.materializedValues ??= new WeakMap<object, unknown>()

    return this.materializedValues
  }

  private draftStateFor(value: object): DraftState | undefined {
    return this.statesByHandle.get(value) ?? this.statesByBase.get(value)
  }

  private cloneSpecialValueAfterMiss(value: object, kind: CloneOnReadKind): object {
    if (
      (kind === OBJECT_KIND_DATA_VIEW || kind === OBJECT_KIND_TYPED_ARRAY) &&
      this.specialCloneCloneToBase.has((value as ArrayBufferView).buffer)
    ) {
      // Recipe-created views already use a writable draft buffer. Keep that backing store;
      // finalization will rebind the view if the unchanged buffer returns to its base.
      return value
    }

    const replacement = snapshotObjectByKindAfterMiss(kind, value, this.specialCloneBaseToClone)

    this.specialCloneCloneToBase.set(replacement, value)
    if (kind === OBJECT_KIND_DATA_VIEW || kind === OBJECT_KIND_TYPED_ARRAY) {
      // Snapshotting a view also clones its buffer. Register that indirect clone
      // so a later buffer read finalizes to the same backing store as the view.
      this.specialCloneCloneToBase.set(
        (replacement as ArrayBufferView).buffer,
        (value as ArrayBufferView).buffer,
      )
    }
    return replacement
  }

  createDraft<T>(current: T): T {
    if (!isObject(current)) {
      return current
    }

    const kind = objectKindOf(current)

    switch (kind) {
      case OBJECT_KIND_ARRAY:
      case OBJECT_KIND_MAP:
      case OBJECT_KIND_PLAIN:
      case OBJECT_KIND_SET:
        return this.createDraftHandleAfterMiss(current, kind) as T
      default:
        return this.cloneSpecialValueAfterMiss(current, kind) as T
    }
  }

  private createDraftHandleAfterMiss(value: object, kind: DraftableKind): object {
    switch (kind) {
      case OBJECT_KIND_ARRAY:
      case OBJECT_KIND_PLAIN: {
        const state: ObjectArrayDraftState = {
          base: value,
          children: new Map<PropertyKey, unknown>(),
          context: this,
          copy: undefined,
          kind,
          modified: false,
          proxy: undefined,
        }
        this.statesByBase.set(value, state)
        return ensureObjectArrayProxy(state)
      }
      case OBJECT_KIND_MAP: {
        const state: MapDraftState = {
          base: value,
          children: new Map<unknown, unknown>(),
          context: this,
          copy: undefined,
          kind,
          modified: false,
          wrapper: undefined,
        }
        this.statesByBase.set(value, state)
        return ensureDraftMap(state)
      }
      case OBJECT_KIND_SET: {
        const state: SetDraftState = {
          base: value,
          context: this,
          copy: undefined,
          kind,
          modified: false,
          wrapper: undefined,
        }
        this.statesByBase.set(value, state)
        return ensureDraftSet(state)
      }
    }
  }

  materializeChild<K>(children: Map<K, unknown>, key: K, value: object): object {
    if (this.statesByHandle.has(value) || this.specialCloneCloneToBase.has(value)) {
      children.set(key, value)
      return value
    }

    const existingState = this.statesByBase.get(value)

    if (existingState !== undefined) {
      const draft = draftHandleOf(existingState)!

      children.set(key, draft)
      return draft
    }

    const existingClone = this.specialCloneBaseToClone.get(value)

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
        child = this.createDraftHandleAfterMiss(value, kind)
        break
      case OBJECT_KIND_ARRAY_BUFFER:
      case OBJECT_KIND_DATA_VIEW:
      case OBJECT_KIND_DATE:
      case OBJECT_KIND_TYPED_ARRAY:
        child = this.cloneSpecialValueAfterMiss(value, kind)
        break
      default:
        // Defensive fallback: objectKindOf() currently classifies every object into one of the
        // branches above, but keeping the raw value here avoids surprising breakage if the shared
        // classifier broadens before this call site is updated.
        //
        // The supported public API does not intentionally route values here, so a direct test
        // would be white-box and coupled to internal classifier broadening.
        return value
    }

    children.set(key, child)
    return child
  }

  isSameDraftValue(currentValue: unknown, value: unknown): boolean {
    // Structural handles represent their bases; special writable clones remain distinct values.
    const currentBase = isObject(currentValue)
      ? (this.statesByHandle.get(currentValue)?.base ?? currentValue)
      : currentValue
    const assignedBase = isObject(value) ? (this.statesByHandle.get(value)?.base ?? value) : value
    return Object.is(currentBase, assignedBase)
  }

  resolveMapKey(source: Map<unknown, unknown>, key: unknown): unknown {
    // Newly assigned maps may store handles, while existing maps normally store bases.
    if (source.has(key) || !isObject(key)) {
      return key
    }

    const draftState = this.statesByHandle.get(key)
    if (draftState !== undefined) {
      return draftState.base
    }

    const baseState = this.statesByBase.get(key)
    const handle = baseState === undefined ? undefined : draftHandleOf(baseState)
    return handle !== undefined && source.has(handle) ? handle : key
  }

  resolveSetMember(source: Set<unknown>, value: unknown): unknown {
    if (source.has(value)) {
      return value
    }

    if (!isObject(value)) {
      return LOOKUP_MISS
    }

    const draftState = this.statesByHandle.get(value)

    if (draftState !== undefined) {
      const baseValue = draftState.base

      if (source.has(baseValue)) {
        return baseValue
      }

      return LOOKUP_MISS
    }

    const baseState = this.statesByBase.get(value)

    if (baseState !== undefined) {
      const handle = draftHandleOf(baseState)
      if (handle !== undefined && source.has(handle)) {
        return handle
      }
    }

    return LOOKUP_MISS
  }

  materializeResult(value: object): unknown {
    const plan: MaterializationPlan = {
      clonesSpecialValues: false,
      deferred: new Map<object, () => unknown>(),
      parent: undefined,
      parents: new WeakMap<object, Set<object>>(),
      pending: [],
      required: new WeakSet<object>(),
    }
    this.materializationPlan = plan
    this.materializationRequired = undefined
    let result: unknown
    try {
      // Discover clone requirements using the same slot rules as final publication.
      // Only previously skipped subtrees need expansion when a new requirement arrives.
      result = this.materializeValue(value)
      for (let index = 0; index < plan.pending.length; index += 1) {
        const node = plan.pending[index]
        const expand = plan.deferred.get(node)
        if (expand !== undefined) {
          plan.deferred.delete(node)
          this.getMaterializedValues().delete(node)
          expand()
        }
      }
    } finally {
      this.materializationPlan = undefined
      this.materializationRequired = undefined
      this.materializedValues = undefined
    }
    return plan.clonesSpecialValues ? this.materializeValue(value) : result
  }

  private requireMaterialization(value: object, plan: MaterializationPlan): void {
    const pending = [value]
    for (let index = 0; index < pending.length; index += 1) {
      const node = pending[index]
      if (plan.required.has(node)) {
        continue
      }
      plan.required.add(node)
      this.getMaterializationRequired().set(node, true)
      if (plan.deferred.has(node)) {
        plan.pending.push(node)
      }
      const parents = plan.parents.get(node)
      if (parents !== undefined) {
        for (const parent of parents) {
          pending.push(parent)
        }
      }
    }
  }

  materializeValue(value: unknown): unknown {
    if (!isObject(value)) {
      return value
    }

    const memo = this.getMaterializedValues()
    const cached = memo.get(value)

    if (cached !== undefined) {
      return cached
    }

    return this.materializeUncachedObjectValue(value)
  }

  needsMaterialization(value: unknown, knownKind: ObjectKind | undefined = undefined): boolean {
    const plan = this.materializationPlan
    if (plan?.parent !== undefined && isObject(value)) {
      const child = this.draftStateFor(value)?.base ?? value
      let parents = plan.parents.get(child)
      if (parents === undefined) {
        parents = new Set<object>()
        plan.parents.set(child, parents)
      }
      parents.add(plan.parent)
      if (plan.required.has(child)) {
        this.requireMaterialization(plan.parent, plan)
      }
    }
    if (this.materializationVisited !== undefined) {
      return this.checkMaterialization(value, knownKind, this.materializationVisited)
    }

    const visited = new Set<object>()
    this.materializationVisited = visited

    try {
      const result = this.checkMaterialization(value, knownKind, visited)

      // A cycle guard is provisional. Cache negative answers only when the entire
      // reachable search found no changes; a later sibling may change an ancestor.
      if (!result) {
        const memo = this.getMaterializationRequired()
        for (const node of visited) {
          memo.set(node, false)
        }
      }

      return result
    } finally {
      this.materializationVisited = undefined
    }
  }

  private checkMaterialization(
    value: unknown,
    knownKind: ObjectKind | undefined,
    visited: Set<object>,
  ): boolean {
    if (!isObject(value)) {
      return false
    }

    // A handle needs unwrapping even when its base is unchanged. Do not cache
    // this answer against the base: materializeState can still reuse that base.
    if (this.statesByHandle.has(value)) {
      return true
    }

    const state = this.draftStateFor(value)
    const base = state?.base ?? value
    const memo = this.getMaterializationRequired()
    if (this.materializationPlan?.required.has(base) === true) {
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
        (this.specialCloneCloneToBase.has(value) || this.specialCloneBaseToClone.has(value)))
    ) {
      memo.set(base, true)
      return true
    }

    if (visited.has(base)) {
      return false
    }

    visited.add(base)
    const result = this.walkDescendantsForMaterialization(base, state?.kind ?? knownKind)

    if (result) {
      memo.set(base, true)
    }

    return result
  }

  private shouldReuseCurrentBackedCloneOnReadSpecial(
    value: object,
    kind: CloneOnReadKind,
  ): boolean {
    if (this.untrackedSpecialsToClone.has(value)) {
      return false
    }
    const mappedClone = this.specialCloneBaseToClone.get(value)

    if (kind === OBJECT_KIND_DATA_VIEW || kind === OBJECT_KIND_TYPED_ARRAY) {
      const buffer = (value as ArrayBufferView).buffer
      if (this.untrackedSpecialsToClone.has(buffer)) {
        return false
      }
      if (this.specialCloneCloneToBase.has(buffer)) {
        return this.materializeValue(buffer) === buffer
      }
      const mappedBufferClone = this.specialCloneBaseToClone.get(buffer)

      if (
        mappedBufferClone !== undefined &&
        !isSpecialValueEquivalent(buffer, mappedBufferClone, OBJECT_KIND_ARRAY_BUFFER)
      ) {
        return false
      }
    }

    if (mappedClone !== undefined) {
      return isSpecialValueEquivalent(value, mappedClone, kind)
    }

    return true
  }

  private materializeArray(
    source: unknown[],
    state: ObjectArrayDraftState | undefined,
    memoKey: object,
    currentBackedBase?: unknown[],
  ): unknown[] {
    const replacement = new Array<unknown>(source.length)
    this.getMaterializedValues().set(memoKey, replacement)
    const children = state?.children
    const base = (state?.base as unknown[] | undefined) ?? currentBackedBase

    for (let index = 0; index < source.length; index += 1) {
      if (!(index in source)) {
        continue
      }

      const childKey = String(index)
      const childDraft = children?.get(childKey)
      const sourceValue = source[index]
      const isCurrentBackedSlot =
        childDraft === undefined &&
        base !== undefined &&
        index in base &&
        Object.is(sourceValue, base[index])

      replacement[index] = this.materializeContainerSlot(
        childDraft ?? sourceValue,
        isCurrentBackedSlot,
      )
    }

    return replacement
  }

  private materializeContainerSlot(value: unknown, isCurrentBackedSlot: boolean): unknown {
    if (!isCurrentBackedSlot) {
      return this.materializeValue(value)
    }

    if (!isObject(value)) {
      return value
    }

    const memo = this.getMaterializedValues()
    const cached = memo.get(value)

    if (cached !== undefined) {
      return cached
    }

    const draftState = this.draftStateFor(value)

    if (draftState !== undefined) {
      return this.materializeState(draftState, value)
    }

    const specialCloneBase = this.specialCloneCloneToBase.get(value)

    if (specialCloneBase !== undefined) {
      const finalized = isSpecialValueEquivalent(specialCloneBase, value) ? specialCloneBase : value

      memo.set(value, finalized)
      return finalized
    }

    const kind = objectKindOf(value)
    const cloneOnReadKind = cloneOnReadSpecialKind(kind)

    if (
      cloneOnReadKind !== undefined &&
      this.shouldReuseCurrentBackedCloneOnReadSpecial(value, cloneOnReadKind)
    ) {
      memo.set(value, value)
      return value
    }

    return this.materializeUnmanagedUncachedObjectValue(value, kind, value)
  }

  private materializeMap(
    source: Map<unknown, unknown>,
    state: MapDraftState | undefined,
    memoKey: object,
    currentBackedBase?: Map<unknown, unknown>,
  ): Map<unknown, unknown> {
    const replacement = new Map<unknown, unknown>()
    this.getMaterializedValues().set(memoKey, replacement)
    const children = state?.children
    const base = (state?.base as Map<unknown, unknown> | undefined) ?? currentBackedBase

    for (const [key, value] of source) {
      const baseHasKey = base?.has(key) === true
      const finalizedKey = isObject(key) ? this.materializeContainerSlot(key, baseHasKey) : key

      const childDraft = children?.get(key)
      const isCurrentBackedValue =
        childDraft === undefined &&
        baseHasKey &&
        base !== undefined &&
        Object.is(value, base.get(key))
      const finalizedValue = this.materializeContainerSlot(
        childDraft ?? value,
        isCurrentBackedValue,
      )

      replacement.set(finalizedKey, finalizedValue)
    }

    return replacement
  }

  private materializePlainObject(
    source: Record<PropertyKey, unknown>,
    state: ObjectArrayDraftState | undefined,
    memoKey: object,
    currentBackedBase?: Record<PropertyKey, unknown>,
  ): Record<PropertyKey, unknown> {
    const replacement = Object.create(Object.getPrototypeOf(source) as object | null) as Record<
      PropertyKey,
      unknown
    >
    this.getMaterializedValues().set(memoKey, replacement)

    const sourceOwnKeys = ownKeys(source)
    const children = state?.children
    const base = (state?.base as Record<PropertyKey, unknown> | undefined) ?? currentBackedBase

    for (let index = 0; index < sourceOwnKeys.length; index += 1) {
      const key = sourceOwnKeys[index]
      const descriptor = Object.getOwnPropertyDescriptor(source, key)
      const childDraft = children?.get(key)

      if (descriptor !== undefined && 'value' in descriptor) {
        const baseDescriptor =
          childDraft === undefined && base !== undefined
            ? Object.getOwnPropertyDescriptor(base, key)
            : undefined
        const isCurrentBackedSlot =
          childDraft === undefined &&
          baseDescriptor !== undefined &&
          'value' in baseDescriptor &&
          Object.is(descriptor.value, baseDescriptor.value)

        descriptor.value = this.materializeContainerSlot(
          childDraft ?? descriptor.value,
          isCurrentBackedSlot,
        )
        Object.defineProperty(replacement, key, descriptor)
        continue
      }

      const sourceValue = source[key]
      const isCurrentBackedSlot =
        childDraft === undefined && base !== undefined && Object.is(sourceValue, base[key])

      replacement[key] = this.materializeContainerSlot(
        childDraft ?? sourceValue,
        isCurrentBackedSlot,
      )
    }

    return replacement
  }

  private materializeSet(
    source: Set<unknown>,
    state: SetDraftState | undefined,
    memoKey: object,
    currentBackedBase?: Set<unknown>,
  ): Set<unknown> {
    const replacement = new Set<unknown>()
    this.getMaterializedValues().set(memoKey, replacement)
    const base = (state?.base as Set<unknown> | undefined) ?? currentBackedBase

    for (const entry of source) {
      replacement.add(this.materializeContainerSlot(entry, base?.has(entry) === true))
    }

    return replacement
  }

  private materializeDraftableObject(
    kind: DraftableKind,
    source: object,
    state: DraftState | undefined,
    memoKey: object,
    currentBackedBase?: object,
  ): object {
    switch (kind) {
      case OBJECT_KIND_ARRAY:
        return this.materializeArray(
          source as unknown[],
          state as ObjectArrayDraftState | undefined,
          memoKey,
          currentBackedBase as unknown[] | undefined,
        )
      case OBJECT_KIND_MAP:
        return this.materializeMap(
          source as Map<unknown, unknown>,
          state as MapDraftState | undefined,
          memoKey,
          currentBackedBase as Map<unknown, unknown> | undefined,
        )
      case OBJECT_KIND_PLAIN:
        return this.materializePlainObject(
          source as Record<PropertyKey, unknown>,
          state as ObjectArrayDraftState | undefined,
          memoKey,
          currentBackedBase as Record<PropertyKey, unknown> | undefined,
        )
      case OBJECT_KIND_SET:
        return this.materializeSet(
          source as Set<unknown>,
          state as SetDraftState | undefined,
          memoKey,
          currentBackedBase as Set<unknown> | undefined,
        )
    }
  }

  private materializeState(state: DraftState, knownUncachedValue?: object): object {
    const memo = this.getMaterializedValues()

    if (knownUncachedValue !== state.base) {
      const cached = memo.get(state.base)

      if (cached !== undefined) {
        return cached as object
      }
    }

    // Monotonic model: a draft that is itself unmodified reuses base as-is unless a descendant
    // reached through its base graph forces materialization (shared draft touched via a sibling,
    // clone-on-read special, etc.). `needsMaterialization(...)` centralizes that recursive check.
    if (!state.modified && !this.needsMaterialization(state.base)) {
      this.materializationPlan?.deferred.set(state.base, () => this.materializeState(state))
      memo.set(state.base, state.base)
      return state.base
    }

    const source = draftValue(state)

    return this.materializeDraftableObject(state.kind, source, state, state.base)
  }

  private materializeUncachedObjectValue(
    value: object,
    knownKind: ObjectKind | undefined = undefined,
    currentBackedBase?: object,
  ): unknown {
    const draftState = this.draftStateFor(value)

    if (draftState !== undefined) {
      return this.materializeState(draftState, value)
    }

    return this.materializeUnmanagedUncachedObjectValue(value, knownKind, currentBackedBase)
  }

  private materializeUnmanagedUncachedObjectValue(
    value: object,
    knownKind: ObjectKind | undefined = undefined,
    currentBackedBase?: object,
  ): unknown {
    const memo = this.getMaterializedValues()
    const specialCloneBase = this.specialCloneCloneToBase.get(value)

    if (specialCloneBase !== undefined) {
      const finalized = isSpecialValueEquivalent(specialCloneBase, value) ? specialCloneBase : value

      memo.set(value, finalized)
      return finalized
    }

    const mappedClone = this.specialCloneBaseToClone.get(value)

    if (mappedClone !== undefined) {
      const finalized = this.materializeValue(mappedClone)
      memo.set(value, finalized)
      return finalized
    }

    const kind = knownKind ?? objectKindOf(value)
    if (cloneOnReadSpecialKind(kind) !== undefined && !this.untrackedSpecialsToClone.has(value)) {
      this.untrackedSpecialsToClone.add(value)
      if (this.materializationPlan !== undefined) {
        this.materializationPlan.clonesSpecialValues = true
        this.requireMaterialization(value, this.materializationPlan)
      }
    }

    switch (kind) {
      case OBJECT_KIND_ARRAY:
      case OBJECT_KIND_MAP:
      case OBJECT_KIND_PLAIN:
      case OBJECT_KIND_SET:
        if (!this.needsMaterialization(value, kind)) {
          this.materializationPlan?.deferred.set(value, () =>
            this.materializeUnmanagedUncachedObjectValue(value, kind, currentBackedBase),
          )
          memo.set(value, value)
          return value
        }

        return this.materializeDraftableObject(kind, value, undefined, value, currentBackedBase)
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
          this.materializeValue(sourceView.buffer) as ArrayBuffer,
        )
        memo.set(value, replacement)
        return replacement
      }
      case OBJECT_KIND_DATE: {
        const replacement = new Date((value as Date).getTime())
        memo.set(value, replacement)
        return replacement
      }
    }
  }

  private walkDescendantsForMaterialization(
    value: object,
    knownKind: ObjectKind | undefined = undefined,
  ): boolean {
    const plan = this.materializationPlan
    const previousParent = plan?.parent
    if (plan !== undefined) {
      plan.parent = value
    }
    try {
      return this.checkDescendantsForMaterialization(value, knownKind)
    } finally {
      if (plan !== undefined) {
        plan.parent = previousParent
      }
    }
  }

  private checkDescendantsForMaterialization(
    value: object,
    knownKind: ObjectKind | undefined,
  ): boolean {
    switch (knownKind ?? objectKindOf(value)) {
      case OBJECT_KIND_DATA_VIEW:
      case OBJECT_KIND_TYPED_ARRAY:
        // An unread view can still depend on a buffer changed through another view.
        return this.needsMaterialization((value as ArrayBufferView).buffer)
      case OBJECT_KIND_ARRAY: {
        const arrayValue = value as unknown[]

        for (let index = 0; index < arrayValue.length; index += 1) {
          if (!(index in arrayValue)) {
            continue
          }

          if (this.needsMaterialization(arrayValue[index])) {
            return true
          }
        }

        return false
      }
      case OBJECT_KIND_MAP:
        for (const [key, entry] of value as Map<unknown, unknown>) {
          if (this.needsMaterialization(key) || this.needsMaterialization(entry)) {
            return true
          }
        }

        return false
      case OBJECT_KIND_PLAIN: {
        const objectValue = value as Record<PropertyKey, unknown>
        const objectOwnKeys = ownKeys(value)

        for (let index = 0; index < objectOwnKeys.length; index += 1) {
          if (this.needsMaterialization(objectValue[objectOwnKeys[index]])) {
            return true
          }
        }

        return false
      }
      case OBJECT_KIND_SET:
        for (const entry of value as Set<unknown>) {
          if (this.needsMaterialization(entry)) {
            return true
          }
        }

        return false
      default:
        return false
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
 * Replacement values can contain both draft values and ordinary JavaScript values. When
 * finalization rebuilds a replacement, it may also copy ordinary `Date`, `ArrayBuffer`,
 * `DataView`, and typed-array values. Every reference to the same value resolves consistently,
 * including references inside nested containers. A container may therefore be rebuilt even if
 * the recipe did not modify it directly. This preserves sharing within the result; it does not
 * make the entire result detached from its inputs.
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
  const context = new PatchContext()
  const draft = context.createDraft(current)

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

  if (!context.needsMaterialization(result)) {
    return result
  }

  return context.materializeResult(result) as R
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
