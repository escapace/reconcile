import { setOwnProperty } from './set-own-property'
import { isObject, ownKeys } from 'coastal'

import { cloneBufferView } from './clone-buffer-view'
import type { ObjectKind } from './object-kind'
import {
  OBJECT_KIND_ARRAY,
  OBJECT_KIND_ARRAY_BUFFER,
  OBJECT_KIND_DATA_VIEW,
  OBJECT_KIND_DATE,
  OBJECT_KIND_MAP,
  OBJECT_KIND_PLAIN,
  OBJECT_KIND_SET,
  OBJECT_KIND_TYPED_ARRAY,
  objectKindOf,
} from './object-kind'
import { snapshot, snapshotObjectByKindAfterMiss } from './snapshot'

type CurrentObjectMap = WeakMap<object, ObjectKind>

// Collect reachable identities and their kinds for overlap detection and current-side
// dispatch. Register before descending so cycles terminate without a separate visited set.
function collectObjectKinds(value: unknown, objects: CurrentObjectMap): void {
  // Primitives and already-recorded objects cannot add any new reachable identities. Using
  // `objects.has` as the cycle guard avoids a parallel WeakSet on the hot prepass path.
  if (!isObject(value) || objects.has(value)) {
    return
  }

  // Record the object before descending so cycles and repeated references terminate cleanly.
  const kind = objectKindOf(value)
  objects.set(value, kind)

  switch (kind) {
    case OBJECT_KIND_ARRAY: {
      const arrayValue = value as unknown[]
      for (let index = 0; index < arrayValue.length; index += 1) {
        if (index in arrayValue) {
          collectObjectKinds(arrayValue[index], objects)
        }
      }
      return
    }
    case OBJECT_KIND_ARRAY_BUFFER:
    case OBJECT_KIND_DATE:
      return
    case OBJECT_KIND_DATA_VIEW:
    case OBJECT_KIND_TYPED_ARRAY:
      collectObjectKinds((value as ArrayBufferView).buffer, objects)
      return
    case OBJECT_KIND_MAP: {
      for (const [key, entry] of (value as Map<unknown, unknown>).entries()) {
        collectObjectKinds(key, objects)
        collectObjectKinds(entry, objects)
      }
      return
    }
    case OBJECT_KIND_PLAIN: {
      const objectValue = value as Record<PropertyKey, unknown>
      const objectOwnKeys = ownKeys(objectValue)
      for (let index = 0; index < objectOwnKeys.length; index += 1) {
        collectObjectKinds(objectValue[objectOwnKeys[index]], objects)
      }
      return
    }
    case OBJECT_KIND_SET: {
      for (const entry of (value as Set<unknown>).values()) {
        collectObjectKinds(entry, objects)
      }
      return
    }
  }
}

// Object children always visit their descendants. Equal identities do not prove
// that another branch will preserve those descendants' next-side topology.
function reconcileEntry(
  currentEntry: unknown,
  nextEntry: unknown,
  currentObjects: CurrentObjectMap,
  currentToNext: WeakMap<object, object>,
  nextToResult: WeakMap<object, object>,
): unknown {
  return isObject(nextEntry)
    ? reconcileKnownNextObject(currentEntry, nextEntry, currentObjects, currentToNext, nextToResult)
    : nextEntry
}

// ── Kind-specific handlers ────────────────────────────────────────────────────

/**
 * Reconciles a plain object while publishing the next object's own-key order.
 *
 * @remarks
 * This handler separates value reconciliation from key-order enforcement. It first compares the
 * current and next own-key sequences across their shared prefix. When that prefix is aligned, the
 * handler reconciles values by key, records only the entries whose reconciled values changed, then
 * applies those writes and deletes any trailing current keys. When the shared prefix diverges, the
 * handler reconciles all next-key values into a scratch array, deletes every current own key, and
 * rewrites the object in next-key order.
 *
 * The result keeps the current object's identity and prototype. Only the object's published own-key
 * order and reconciled property values are updated to match the next graph.
 */
function reconcilePlainObject(
  currentValue: object,
  nextValue: object,
  currentObjects: CurrentObjectMap,
  currentToNext: WeakMap<object, object>,
  nextToResult: WeakMap<object, object>,
): object {
  const currentObject = currentValue as Record<PropertyKey, unknown>
  const nextObject = nextValue as Record<PropertyKey, unknown>
  const currentOwnKeys = ownKeys(currentObject)
  const nextOwnKeys = ownKeys(nextObject)
  const currentLength = currentOwnKeys.length
  const nextLength = nextOwnKeys.length
  const overlap = Math.min(currentLength, nextLength)
  let aligned = true

  // Treat trailing additions and removals as aligned. Only a mismatch inside the shared prefix
  // forces the full key-order rebuild path.
  for (let index = 0; index < overlap; index += 1) {
    if (currentOwnKeys[index] !== nextOwnKeys[index]) {
      aligned = false
      break
    }
  }

  let changedEntries: unknown[] | undefined
  const reconciledEntries = aligned ? undefined : new Array<unknown>(nextLength)

  for (let index = 0; index < nextLength; index += 1) {
    const key = nextOwnKeys[index]
    const currentEntry =
      key === '__proto__' && !Object.prototype.hasOwnProperty.call(currentObject, key)
        ? undefined
        : currentObject[key]
    const nextEntry = nextObject[key]
    const reconciledEntry = reconcileEntry(
      currentEntry,
      nextEntry,
      currentObjects,
      currentToNext,
      nextToResult,
    )

    if (reconciledEntries === undefined) {
      // Incremental path: reconcile values in next-key order, but defer writes until the scan is
      // complete so unchanged entries do not trigger redundant assignments. Only check property
      // presence in the one ambiguous case where the reconciled value is still `Object.is`-equal
      // to the current read: trailing additions may still need an own property materialized.
      if (
        !Object.is(reconciledEntry, currentEntry) ||
        !Object.prototype.hasOwnProperty.call(currentObject, key)
      ) {
        changedEntries ??= []
        changedEntries.push(key, reconciledEntry)
      }
    } else {
      reconciledEntries[index] = reconciledEntry
    }
  }

  if (reconciledEntries === undefined) {
    if (changedEntries !== undefined) {
      // Apply only the entries whose reconciled values changed.
      for (let index = 0; index < changedEntries.length; index += 2) {
        setOwnProperty(
          currentObject,
          changedEntries[index] as PropertyKey,
          changedEntries[index + 1],
        )
      }
    }

    // Shared-prefix alignment allows trailing current keys to be removed without rewriting the
    // whole object.
    for (let index = nextLength; index < currentLength; index += 1) {
      Reflect.deleteProperty(currentObject, currentOwnKeys[index])
    }

    return currentObject
  }

  // Key order diverged inside the shared prefix, so the object must be republished in exact
  // next-key order.

  // Remove all current keys before repopulating to ensure the resulting own-key order matches
  // the next object exactly.
  for (let index = 0; index < currentLength; index += 1) {
    Reflect.deleteProperty(currentObject, currentOwnKeys[index])
  }

  for (let index = 0; index < nextLength; index += 1) {
    setOwnProperty(currentObject, nextOwnKeys[index], reconciledEntries[index])
  }

  return currentObject
}

/**
 * Reconciles an array by index while preserving sparse holes from the next array.
 *
 * @remarks
 * The handler first publishes the next length on the current array, then walks each next index in
 * order. Present indices are reconciled through {@link reconcileEntry}. Missing next indices
 * are kept as holes by deleting the corresponding current property when it exists. Writes are
 * guarded with `Object.is` so unchanged reconciled entries do not trigger redundant assignments on
 * reactive or proxied arrays.
 */
function reconcileArray(
  currentValue: object,
  nextValue: object,
  currentObjects: CurrentObjectMap,
  currentToNext: WeakMap<object, object>,
  nextToResult: WeakMap<object, object>,
): unknown[] {
  const currentArray = currentValue as unknown[]
  const nextArray = nextValue as unknown[]
  const nextLength = nextArray.length
  // Publish the next length once before visiting individual indices.
  currentArray.length = nextLength

  for (let index = 0; index < nextLength; index += 1) {
    if (index in nextArray) {
      const currentEntry = currentArray[index]
      const nextEntry = nextArray[index]
      const reconciledEntry = reconcileEntry(
        currentEntry,
        nextEntry,
        currentObjects,
        currentToNext,
        nextToResult,
      )

      // Avoid redundant writes when reconciliation keeps the existing entry identity. Array slots
      // need one extra check in the single ambiguous case where both reads produce `undefined`: a
      // present next-side `undefined` must still materialize when the current slot is a hole.
      if (
        !Object.is(reconciledEntry, currentEntry) ||
        (reconciledEntry === undefined && !(index in currentArray))
      ) {
        currentArray[index] = reconciledEntry
      }
    } else if (index in currentArray) {
      // Preserve a next-array hole by removing the current indexed property.
      Reflect.deleteProperty(currentArray, index)
    }
  }

  return currentArray
}

/**
 * Reconciles a map by ordinal position rather than by key lookup.
 *
 * @remarks
 * The i-th current entry is paired with the i-th next entry. Each paired key and value is
 * reconciled through {@link reconcileEntry}. The handler stays on a no-allocation path until
 * the first positional change or size mismatch is observed. At that point it allocates a flat
 * scratch array, backfills the unchanged prefix from the current map, stores the remaining
 * reconciled entries, then clears and rebuilds the map once at the end.
 *
 * When all reconciled keys and values remain `Object.is`-equal to the current entries and the map
 * sizes already match, the function returns `currentMap` unchanged.
 */
function reconcileMap(
  currentValue: object,
  nextValue: object,
  currentObjects: CurrentObjectMap,
  currentToNext: WeakMap<object, object>,
  nextToResult: WeakMap<object, object>,
): Map<unknown, unknown> {
  const currentMap = currentValue as Map<unknown, unknown>
  const nextMap = nextValue as Map<unknown, unknown>
  const nextSize = nextMap.size
  let reconciledEntries: unknown[] | undefined
  let backfillLimit = 0
  let entryOffset = 0
  const currentEntries = currentMap.entries()

  // Ordinal alignment: compare the i-th current entry with the i-th next entry.
  for (const [nextKey, nextEntry] of nextMap.entries()) {
    const currentEntryPair = currentEntries.next().value
    const currentKey = currentEntryPair?.[0]
    const currentEntry = currentEntryPair?.[1]
    const reconciledKey = reconcileEntry(
      currentKey,
      nextKey,
      currentObjects,
      currentToNext,
      nextToResult,
    )
    const reconciledEntry = reconcileEntry(
      currentEntry,
      nextEntry,
      currentObjects,
      currentToNext,
      nextToResult,
    )

    // Stay on the no-allocation path until the first positional change or until current
    // runs out before next. At that point the map must be rebuilt.
    if (
      reconciledEntries === undefined &&
      (currentEntryPair === undefined ||
        !Object.is(reconciledKey, currentKey) ||
        !Object.is(reconciledEntry, currentEntry))
    ) {
      reconciledEntries = new Array<unknown>(nextSize * 2)
      backfillLimit = entryOffset
    }

    if (reconciledEntries !== undefined) {
      reconciledEntries[entryOffset] = reconciledKey
      reconciledEntries[entryOffset + 1] = reconciledEntry
    }

    entryOffset += 2
  }

  // If no entry changed and sizes already match, keep the current map as-is. Otherwise the
  // reconciled prefix was unchanged but the published size must still change, so build the
  // replacement sequence from that prefix.
  if (reconciledEntries === undefined) {
    if (currentMap.size === nextSize) {
      return currentMap
    }

    reconciledEntries = new Array<unknown>(nextSize * 2)
    backfillLimit = reconciledEntries.length
  }

  if (backfillLimit > 0) {
    const backfillEntries = currentMap.entries()

    for (let backfillOffset = 0; backfillOffset < backfillLimit; backfillOffset += 2) {
      const backfillEntry = backfillEntries.next().value!

      reconciledEntries[backfillOffset] = backfillEntry[0]
      reconciledEntries[backfillOffset + 1] = backfillEntry[1]
    }
  }

  // Apply the rebuild once after every reconciled entry is known.
  currentMap.clear()

  for (let entryOffset = 0; entryOffset < reconciledEntries.length; entryOffset += 2) {
    currentMap.set(reconciledEntries[entryOffset], reconciledEntries[entryOffset + 1])
  }

  return currentMap
}

/**
 * Reconciles a set by ordinal position.
 *
 * @remarks
 * The i-th current value is paired with the i-th next value and reconciled through
 * {@link reconcileEntry}. Like {@link reconcileMap}, this handler delays allocation until
 * the first positional change or size mismatch. If a rebuild becomes necessary, it backfills the
 * unchanged prefix from the current set, appends the remaining reconciled values, then clears and
 * repopulates the set once.
 *
 * When all reconciled values remain `Object.is`-equal to the current values and the set sizes
 * already match, the function returns `currentSet` unchanged.
 */
function reconcileSet(
  currentValue: object,
  nextValue: object,
  currentObjects: CurrentObjectMap,
  currentToNext: WeakMap<object, object>,
  nextToResult: WeakMap<object, object>,
): Set<unknown> {
  const currentSet = currentValue as Set<unknown>
  const nextSet = nextValue as Set<unknown>
  const nextSize = nextSet.size
  let reconciledEntries: unknown[] | undefined
  let backfillLimit = 0
  let index = 0
  const currentEntries = currentSet.values()

  // Ordinal alignment: compare the i-th current value with the i-th next value.
  for (const nextEntry of nextSet.values()) {
    const currentStep = currentEntries.next()
    const currentEntry = currentStep.value
    const reconciledEntry = reconcileEntry(
      currentEntry,
      nextEntry,
      currentObjects,
      currentToNext,
      nextToResult,
    )

    // Stay on the no-allocation path until the first positional change or until current
    // runs out before next. At that point the set must be rebuilt.
    if (
      reconciledEntries === undefined &&
      (currentStep.done === true || !Object.is(reconciledEntry, currentEntry))
    ) {
      reconciledEntries = new Array<unknown>(nextSize)
      backfillLimit = index
    }

    if (reconciledEntries !== undefined) {
      reconciledEntries[index] = reconciledEntry
    }

    index += 1
  }

  // If no entry changed and sizes already match, keep the current set as-is. Otherwise the
  // reconciled prefix was unchanged but the published size must still change, so build the
  // replacement sequence from that prefix.
  if (reconciledEntries === undefined) {
    if (currentSet.size === nextSize) {
      return currentSet
    }

    reconciledEntries = new Array<unknown>(nextSize)
    backfillLimit = nextSize
  }

  if (backfillLimit > 0) {
    const backfillEntries = currentSet.values()

    for (let backfillIndex = 0; backfillIndex < backfillLimit; backfillIndex += 1) {
      reconciledEntries[backfillIndex] = backfillEntries.next().value
    }
  }

  // Apply the rebuild once after every reconciled value is known.
  currentSet.clear()

  for (let entryIndex = 0; entryIndex < reconciledEntries.length; entryIndex += 1) {
    currentSet.add(reconciledEntries[entryIndex])
  }

  return currentSet
}

/**
 * Reconciles an `ArrayBuffer` in place when the published byte length is unchanged.
 *
 * @remarks
 * Equal-length buffers copy next bytes into the current buffer and keep its identity. A byte-length
 * mismatch forces replacement because an `ArrayBuffer` cannot be resized in place. Replacement
 * buffers are written into `nextToResult` so later `DataView` and typed-array reconciliations that
 * reference the same next buffer reuse the same cloned backing store.
 */
function reconcileArrayBuffer(
  currentValue: object,
  nextValue: object,
  nextToResult: WeakMap<object, object>,
): ArrayBuffer {
  const currentBuffer = currentValue as ArrayBuffer
  const nextBuffer = nextValue as ArrayBuffer

  // Equal-length buffers can publish next bytes into the existing backing store.
  if (currentBuffer.byteLength !== nextBuffer.byteLength) {
    const replacement = nextBuffer.slice(0)

    // Cache the replacement so every later next-side alias of this buffer resolves to the same
    // reconciled backing store.
    nextToResult.set(nextValue, replacement)
    return replacement
  }

  new Uint8Array(currentBuffer).set(new Uint8Array(nextBuffer))
  return currentBuffer
}

/**
 * Reconciles a `DataView` or typed-array view after reconciling its backing buffer.
 *
 * @remarks
 * The backing buffer is an aligned child of the view, so it must be reconciled first. The current
 * view can be kept only when the reconciled buffer identity, constructor, byte offset, and byte
 * length all still match the next view. Otherwise the handler clones the next view over the
 * reconciled buffer and overwrites the provisional `nextToResult` cache entry with that
 * replacement. This preserves sharing when the same next view object is encountered again later.
 */
function reconcileBufferView(
  currentValue: object,
  nextValue: object,
  currentObjects: CurrentObjectMap,
  currentToNext: WeakMap<object, object>,
  nextToResult: WeakMap<object, object>,
): ArrayBufferView {
  const currentView = currentValue as ArrayBufferView
  const nextView = nextValue as ArrayBufferView

  // Reconcile the aligned buffer child before checking whether the current view can survive.
  const reconciledBuffer = reconcileEntry(
    currentView.buffer,
    nextView.buffer,
    currentObjects,
    currentToNext,
    nextToResult,
  ) as ArrayBuffer

  // Keep the current view only when the reconciled backing store and the published view shape are
  // still compatible.
  if (
    currentView.buffer === reconciledBuffer &&
    currentView.constructor === nextView.constructor &&
    currentView.byteOffset === nextView.byteOffset &&
    currentView.byteLength === nextView.byteLength
  ) {
    return currentView
  }

  const replacement = cloneBufferView(nextView, reconciledBuffer)

  // reconcileObjectByKind pre-registered nextView -> currentView. Overwrite that provisional cache
  // entry so later encounters with the same next view return the replacement instead.
  nextToResult.set(nextView, replacement)
  return replacement
}

/**
 * Dispatches object reconciliation to the handler for the shared runtime kind.
 *
 * @remarks
 * The current-to-next and next-to-result witness maps are updated before dispatch. That early
 * registration marks the current object as consumed and caches the provisional result for the next
 * object before any child recursion begins. Cycles and repeated references depend on this ordering:
 * a recursive encounter with either object must observe the alignment that is already in progress.
 */
function reconcileObjectByKind(
  kind: ObjectKind,
  currentValue: object,
  nextValue: object,
  currentObjects: CurrentObjectMap,
  currentToNext: WeakMap<object, object>,
  nextToResult: WeakMap<object, object>,
): unknown {
  // Record the alignment before descending so recursive re-entry through cycles or sharing sees the
  // in-progress mapping immediately.
  currentToNext.set(currentValue, nextValue)
  nextToResult.set(nextValue, currentValue)

  switch (kind) {
    case OBJECT_KIND_ARRAY:
      return reconcileArray(currentValue, nextValue, currentObjects, currentToNext, nextToResult)
    case OBJECT_KIND_ARRAY_BUFFER:
      return reconcileArrayBuffer(currentValue, nextValue, nextToResult)
    case OBJECT_KIND_DATA_VIEW:
    case OBJECT_KIND_TYPED_ARRAY:
      return reconcileBufferView(
        currentValue,
        nextValue,
        currentObjects,
        currentToNext,
        nextToResult,
      )
    case OBJECT_KIND_DATE:
      ;(currentValue as Date).setTime((nextValue as Date).getTime())
      return currentValue
    case OBJECT_KIND_MAP:
      return reconcileMap(currentValue, nextValue, currentObjects, currentToNext, nextToResult)
    case OBJECT_KIND_PLAIN:
      return reconcilePlainObject(
        currentValue,
        nextValue,
        currentObjects,
        currentToNext,
        nextToResult,
      )
    case OBJECT_KIND_SET:
      return reconcileSet(currentValue, nextValue, currentObjects, currentToNext, nextToResult)
  }
}

/**
 * Reconciles a non-equal child value when the next side is already known to be object-like.
 *
 * @remarks
 * This is the nested object-value rule with the non-object next fast exit removed. The check order
 * is part of the topology contract and must not be changed. The function first honors any cached
 * image for `nextValue`, then handles primitive current values, already-consumed current objects,
 * and kind mismatches by snapshotting `nextValue` into a fresh subtree. Only when both sides are
 * object-like, unconsumed, and of the same runtime kind does it descend into
 * {@link reconcileObjectByKind}.
 */
function reconcileKnownNextObject(
  currentValue: unknown,
  nextValue: object,
  currentObjects: CurrentObjectMap,
  currentToNext: WeakMap<object, object>,
  nextToResult: WeakMap<object, object>,
): object {
  const cached = nextToResult.get(nextValue)

  // A cached image for nextValue is authoritative and preserves next-side sharing.
  if (cached !== undefined) {
    return cached
  }

  // One `currentObjects` lookup answers two questions at once: "is `currentValue` a primitive?"
  // and "what is its `ObjectKind`?". `WeakMap.prototype.get` returns `undefined` for non-object
  // keys per spec, and reaching this point implies `currentValue` is either a primitive or a
  // child of an already-reconciled current container (which the prepass walked). Absence is
  // therefore an unambiguous primitive signal here, letting the hot child path skip an explicit
  // `isObject(currentValue)` typeof check while also reusing the cached kind.
  // The function-entry `nextToResult.get(nextValue)` above already proved this is a cache miss,
  // so every snapshot path in this function dispatches through the cache-miss entry point to
  // avoid a redundant lookup inside `snapshot`.
  const currentKind = currentObjects.get(currentValue as object)
  const nextKind = objectKindOf(nextValue)

  // Current was consumed by a different next node. Reusing it here would collapse distinct next
  // topology into one object.
  if (currentKind === undefined || currentToNext.get(currentValue as object) !== undefined) {
    return snapshotObjectByKindAfterMiss(nextKind, nextValue, nextToResult)
  }

  // In-place reconciliation is only valid for matching runtime kinds. The kind has already been
  // computed, so the snapshot path can reuse it directly without a third `objectKindOf` call.
  return currentKind === nextKind
    ? (reconcileObjectByKind(
        currentKind,
        currentValue as object,
        nextValue,
        currentObjects,
        currentToNext,
        nextToResult,
      ) as object)
    : snapshotObjectByKindAfterMiss(nextKind, nextValue, nextToResult)
}

// ── Public entry point ────────────────────────────────────────────────────────

/**
 * Applies `next` onto `current` by updating existing objects and collections when possible.
 *
 * @remarks
 * `reconcile(...)` tries to keep existing identities when the current value can be updated to
 * match the next value. Arrays update by index and preserve sparse holes from `next`. Plain
 * objects update by property key and adopt the next object's own-key order. `Map` and `Set`
 * update by entry order, not by matching keys or values. `Date`, `ArrayBuffer`, `DataView`, and
 * typed arrays update in place only when their published shape stays compatible.
 *
 * The result matches the observable structure of `next`, including plain-object key order,
 * sparse-array holes, cycles, shared references, and `ArrayBuffer` or view aliasing. When one
 * subtree cannot be updated in place, only that subtree is replaced; surrounding parent values may
 * still be reused.
 *
 * Supported values include plain JavaScript objects, arrays, maps, sets, `Date`, `ArrayBuffer`,
 * `DataView`, and typed arrays. The same behavior also applies to common reactive or
 * signal-backed wrappers when they expose object, array, map, or set behavior. Descriptor-level
 * details are not preserved on every path; for example, accessors may keep existing behavior, and
 * retained non-configurable keys may not be removed even when `next` does not contain them.
 *
 * Primitive values are handled directly. If either root is not object-like, or if the root kinds
 * differ, the function returns `next`.
 *
 * @param current - Existing value to update.
 * @param next - Next value to apply onto the existing value.
 * @returns The updated value. This is usually `current`, but it may be `next` or a replacement
 * subtree when in-place update is not possible.
 */
export function reconcile<T extends object>(current: object, next: T): T
export function reconcile<T>(current: unknown, next: T): T
export function reconcile(current: unknown, next: unknown): unknown {
  // Root SameValue equality can return immediately without allocating witness maps.
  if (Object.is(current, next)) {
    return current
  }

  // Primitive boundaries publish next directly. Reconciliation only descends through object-like
  // values.
  if (!isObject(current) || !isObject(next)) {
    return next
  }

  const rootKind = objectKindOf(current)

  // Root kind mismatches replace the whole value instead of preserving the current root.
  if (rootKind !== objectKindOf(next)) {
    return next
  }

  const currentObjects = new WeakMap<object, ObjectKind>()
  collectObjectKinds(current, currentObjects)

  // Shared next graphs need stable edges as well as stable payloads. Per-container
  // snapshots cannot recover an original child identity after an earlier branch replaces it.
  const nextObjects = new Map<object, ObjectKind>()
  collectObjectKinds(next, nextObjects)
  let nextSource = next

  for (const object of nextObjects.keys()) {
    if (currentObjects.has(object)) {
      nextSource = snapshot(next) as object
      break
    }
  }

  // Allocate the witness maps once for the entire reconcile walk, then dispatch into the matching
  // kind handler.
  return reconcileObjectByKind(
    rootKind,
    current,
    nextSource,
    currentObjects,
    new WeakMap<object, object>(),
    new WeakMap<object, object>(),
  )
}
