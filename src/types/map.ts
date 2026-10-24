import { edgeAt } from '../graph/edge'
import { adoptPrototype } from './shared/prototype'
import { freeze, independentBindings, yes } from './shared/empty'
import { noValue } from './shared/empty'
import type {
  CapturePolicy,
  ConstructionPolicy,
  DraftStrategy,
  ImmutablePolicy,
  PublicationPolicy,
  Recognition,
  SnapshotPolicy,
} from '../types'
import { isObject } from '../object-property'
import { resolveWrappedCollectionMember, storageIdentity, type WrappedIndex } from '../adapters/vue'
import type { BaseDraftState, Edge, ExposureFacet, NativePolicy } from '../types'
import { defineType } from './registry'
import { collectionSurface, normalize } from './shared/collection'
import {
  insertedCollectionValue,
  draftState,
  draftValue,
  adoptDraftClass,
  draftChild,
  draftCollectionBase,
  draftWalk,
  eachMapEntry,
  forEachMapEntry,
  wrappedCollection,
} from './shared/draft-collection'
import { emptyEdges } from './shared/empty'
import { draftedForm } from './shared/draft-members'
import {
  builtinMapClear,
  builtinMapDelete,
  builtinMapGet,
  builtinMapHas,
  builtinMapSet,
  builtinMapSize,
  mapStep,
  openBuiltin,
  openMapEntries,
} from '../standard-prototypes'

/** Stable global identity owned by the map module. */
export const MAP_KIND = Symbol.for('@escapace/reconcile/map')

/** The keys of a `Map`. */
function mapKeys(map: object): unknown[] {
  const keys: unknown[] = []
  eachMapEntry(map, (key) => keys.push(key) < 0)
  return keys
}

const mapPolicySurface = /* @__PURE__ */ collectionSurface({
  builtin: {
    open: openMapEntries,
    put: builtinMapSet,
    remove: builtinMapDelete,
    size: builtinMapSize,
    step: mapStep,
  },
  own: {
    open: (current) => (current as Map<unknown, unknown>).entries(),
    put: (current, key, value) => {
      ;(current as Map<unknown, unknown>).set(key, value)
    },
    remove: (current, key) => {
      ;(current as Map<unknown, unknown>).delete(key)
    },
    size: (current) => (current as Map<unknown, unknown>).size,
    step: (iterator) => (iterator as Iterator<unknown>).next(),
  },
  width: 2,
  read: (entry, slot, strict) =>
    strict ? (entry as unknown[])[slot] : (entry as unknown[] | undefined)?.[slot],
})
const mapPolicyWrite: NativePolicy<MapLayout>['freshWrite'] = (node, target, index, resolve) => {
  if (index % 2 === 1)
    builtinMapSet(target, resolve(node.edges[index - 1]), resolve(node.edges[index]))
}
const mapCapture = {
  construction: noValue,
  observe(value, begin, edge) {
    const prototype = Object.getPrototypeOf(value) as object | null
    const wrapped = wrappedCollection(value, prototype)
    begin({ kind: MAP_KIND, prototype })
    forEachMapEntry(
      value,
      (child, key) => {
        edge(key)
        edge(child)
      },
      wrapped,
    )
  },
} satisfies CapturePolicy<MapLayout>

const mapConstruction = {
  bindings: independentBindings,
  allocate: (node) =>
    adoptPrototype(new Map<unknown, unknown>(), node.layout.prototype, Map.prototype),
} satisfies ConstructionPolicy<MapLayout>

export const mapSnapshot = /* @__PURE__ */ (() =>
  /* @__PURE__ */ freeze({
    ...mapCapture,
    /**
     * Streams pairs with only the unmatched canonical key retained between edge events.
     *
     * @remarks
     * Resolve both edges when the value arrives, not when the key first arrives. SnapshotStream
     * proves this pending-key representation preserves finite interleavings with live image changes.
     */
    snapshot(layout, resolve, writer) {
      const target = adoptPrototype(new Map<unknown, unknown>(), layout.prototype, Map.prototype)
      let pending: Edge | undefined
      writer.initialize(layout, target, (edge) => {
        if (pending === undefined) pending = edge
        else {
          builtinMapSet(target, resolve(pending), resolve(edge))
          pending = undefined
        }
      })
    },
  }))() satisfies SnapshotPolicy<MapLayout>

export const mapPublication = /* @__PURE__ */ (() =>
  /* @__PURE__ */ freeze({
    ...mapCapture,
    ...mapConstruction,
    ...mapPolicySurface,
    compatible: yes,
    requirements: emptyEdges,
    seal: (node) => ({ ...node, edges: normalize(node.edges, 2) }),
  }))() satisfies PublicationPolicy<MapLayout>

export const mapImmutable = /* @__PURE__ */ (() => ({
  ...mapConstruction,
  freshWrite: mapPolicyWrite,
  immutable: /* @__PURE__ */ freeze({
    tag: 'structural',
    observeDraft(source, observer) {
      const { base } = observer
      // The prototype is the base's, which a working copy keeps.
      const prototype = Object.getPrototypeOf(base ?? source) as object | null
      observer.begin({ kind: MAP_KIND, prototype })
      // The source is the base or, when it differs, the draft's working copy, a built-in `Map`;
      // only an object from `current` or the recipe can be a wrapper.
      const wrapped = wrappedCollection(base ?? source, prototype)
      forEachMapEntry(
        source,
        (value, key) => {
          const present = base !== undefined && readHas(base, wrapped, key)
          observer.edge(key, undefined, present)
          observer.edge(value, undefined, present && Object.is(value, readGet(base, wrapped, key)))
        },
        source === (base ?? source) && wrapped,
      )
    },
    reuse(node, current, visit) {
      const wrapped = wrappedCollection(current)
      if (readSize(current, wrapped) * 2 !== node.edges.length) return false
      let index = 0
      return !eachMapEntry(
        current,
        (key, value) =>
          !visit(key, edgeAt(node.edges, index++)) || !visit(value, edgeAt(node.edges, index++)),
        wrapped,
      )
    },
  } satisfies ImmutablePolicy<MapLayout>['immutable']),
  someChild(source, _read, test) {
    return eachMapEntry(source, (key, value) => test(key) || test(value))
  },
}))() satisfies ImmutablePolicy<MapLayout>

const mapPolicy = /* @__PURE__ */ (() => ({ ...mapSnapshot, ...mapPublication, ...mapImmutable }))()

/** Identifies ordered Map payloads whose edges alternate keys and values. */
// fallow-ignore-next-line unused-type -- part of the declared type of builtinModules in builtins.ts
export interface MapLayout {
  readonly kind: typeof MAP_KIND
  /** The source's prototype, which a copy keeps. */
  readonly prototype: object | null
}

export const mapExposure: Extract<ExposureFacet, { tag: 'collection' }> = /* @__PURE__ */ freeze({
  tag: 'collection',
  singleton: (value) => new Map([[value, undefined]]),
})

export const mapDraft = /* @__PURE__ */ freeze({
  tag: 'structural',
  handle: (state): object => new DraftMap(state),
  state: (base, context) => ({
    base,
    context,
    copy: undefined,
    handle: undefined,
    kind: MAP_KIND,
    members: { built: undefined, revision: 0, vue: undefined },
    modified: false,
    properties: undefined,
    source() {
      return this.copy ?? this.base
    },
  }),
}) satisfies DraftStrategy<MapDraftState>

const mapRecognition = /* @__PURE__ */ freeze({
  tag: 'predicate',
  test: (value: object) => value instanceof Map,
}) satisfies Recognition

export const mapType = /* @__PURE__ */ defineType<MapLayout, MapDraftState>({
  draft: mapDraft,
  exposure: mapExposure,
  kind: MAP_KIND,
  name: 'map',
  policy: mapPolicy,
  recognition: mapRecognition,
})

// A `Map`'s entries are read through its own methods when it is a wrapper, such as a Vue reactive
// proxy, and otherwise with the built-ins.
const readGet = (map: object, wrapped: boolean, key: unknown): unknown =>
  wrapped ? (map as Map<unknown, unknown>).get(key) : builtinMapGet(map, key)
const readHas = (map: object, wrapped: boolean, key: unknown): boolean =>
  wrapped ? (map as Map<unknown, unknown>).has(key) : builtinMapHas(map, key)
const readSize = (map: object, wrapped: boolean): number =>
  wrapped ? (map as Map<unknown, unknown>).size : builtinMapSize(map)

/** Whether the draft's object is Vue reactive state, read once per draft. */
const vueBase = (state: MapDraftState): boolean =>
  (state.members.vue ??= wrappedCollection(state.base))

/** Whether the draft's entries now, its working copy or its object until it has one, are a
 * wrapper's. */
const wrappedSource = (state: MapDraftState): boolean => state.copy === undefined && vueBase(state)

/**
 * Captures a native Map once, preserving iterator order and key normalization.
 */
function prepareMapCopy(state: MapDraftState): Map<unknown, unknown> {
  if (state.copy !== undefined) {
    return state.copy as Map<unknown, unknown>
  }

  // The working copy keeps the source's class, so methods a subclass adds act on it as on the base;
  // it is filled, and later read and written, with the built-ins.
  const base = state.base as Map<unknown, unknown>
  const copy = new Map<unknown, unknown>()
  forEachMapEntry(
    base,
    (value, key) => {
      builtinMapSet(copy, key, value)
    },
    vueBase(state),
  )
  state.copy = adoptPrototype(copy, Object.getPrototypeOf(base) as object, Map.prototype)
  return state.copy as Map<unknown, unknown>
}

/**
 * Resolves a Map key through its stored identity, draft base, handle, and wrapper equivalence.
 *
 * @returns An existing key when found, otherwise the normalized key for insertion.
 */
function resolveMapKey(
  state: MapDraftState,
  source: Map<unknown, unknown>,
  wrapped: boolean,
  key: unknown,
): unknown {
  const { base, context } = state
  // Newly assigned maps may store handles, while existing maps normally store bases.
  if (!isObject(key) || readHas(source, wrapped, key)) {
    return key
  }

  const drafted = context.statesByIdentity.get(key)
  if (drafted !== undefined) {
    const form = draftedForm(context, drafted, key, source, wrapped, readHas)
    if (form !== undefined) return form
    key = drafted.base
  }
  // A Vue proxy of a key the Map holds is that key, as Vue's methods count it.
  const storage = storageIdentity(key as object)
  if (storage !== key && readHas(source, wrapped, storage)) return storage
  // A copy that a read of a `Date`, buffer, view or URL made counts as its original, as a draft does.
  const copied = context.copyBase(key as object) ?? context.copyOf(key as object)
  if (copied !== undefined && readHas(source, wrapped, copied)) return copied
  return resolveWrappedCollectionMember(source, key as object, base, state.members, mapKeys) ?? key
}

/**
 * Provides copy-on-write Map operations with draft-safe values and key resolution.
 *
 * @remarks
 * Reads and no-op mutations retain the base. Effective mutations copy before writing.
 * Iteration walks the working copy natively; held wrappers remain usable after recipe completion.
 * @internal
 */
const DraftMap = /* @__PURE__ */ (() => {
  class DraftMap extends draftCollectionBase(
    Map.prototype,
    prepareMapCopy as (state: BaseDraftState) => Map<unknown, unknown>,
    // Keys are not drafts: a key is the object stored in the Map.
    (_state, key) => key,
  ) {
    /** Binds the wrapper to its call-local draft state. */
    constructor(state: MapDraftState) {
      super(state)
      adoptDraftClass(this, DraftMap.prototype, Map.prototype, state)
      // A Map result carries only its entries, so the draft refuses new properties.
      Object.preventExtensions(this)
    }

    /** Reads the current collection size without allocating a copy. */
    get size(): number {
      const state = draftState<MapDraftState>(this)
      return readSize(draftValue(state), wrappedSource(state))
    }

    /** Walks the entries of the working copy, each value as its draft. */
    [Symbol.iterator](): IterableIterator<[unknown, unknown]> {
      const state = draftState<MapDraftState>(this)
      const opened = openBuiltin(prepareMapCopy(state), true, 'entries')
      return draftWalk(
        opened.iterator as Iterator<[unknown, unknown]>,
        (entry: [unknown, unknown]) => [entry[0], draftChild(state, entry[1])],
        opened.step,
      )
    }

    /** Clears a nonempty working collection and records an effective change. */
    clear(): void {
      const state = draftState<MapDraftState>(this)

      if (readSize(draftValue(state), wrappedSource(state)) === 0) {
        // Clearing an already-empty map is a true no-op and does not mark the draft modified.
        return
      }

      builtinMapClear(prepareMapCopy(state))
      state.members.revision += 1
      state.modified = true
    }

    /** Deletes an existing Map entry after resolving its identity in the captured copy. */
    delete(key: unknown): boolean {
      const state = draftState<MapDraftState>(this)
      const source = draftValue<Map<unknown, unknown>>(state)
      const wrapped = wrappedSource(state)
      const normalizedKey = resolveMapKey(state, source, wrapped, key)

      if (!readHas(source, wrapped, normalizedKey)) {
        // Deleting a missing key is a true no-op and does not mark the draft modified.
        return false
      }

      const copy = prepareMapCopy(state)
      builtinMapDelete(copy, resolveMapKey(state, copy, false, normalizedKey))
      state.members.revision += 1
      state.modified = true
      return true
    }

    /** Returns a draft-safe Map value while preserving missing-key behavior. */
    get(key: unknown): unknown {
      const state = draftState<MapDraftState>(this)
      const source = draftValue<Map<unknown, unknown>>(state)
      const wrapped = wrappedSource(state)
      const normalizedKey = resolveMapKey(state, source, wrapped, key)
      const value = readGet(source, wrapped, normalizedKey)

      if (value === undefined && !readHas(source, wrapped, normalizedKey)) {
        return undefined
      }

      if (!isObject(value)) {
        return value
      }

      return state.context.materializeChild(value)
    }

    /** Tests membership using draft-base and wrapper identity rules. */
    has(key: unknown): boolean {
      const state = draftState<MapDraftState>(this)
      const source = draftValue<Map<unknown, unknown>>(state)
      const wrapped = wrappedSource(state)
      return readHas(source, wrapped, resolveMapKey(state, source, wrapped, key))
    }

    /** Stores a value unless the resolved entry already represents the same draft value. */
    set(key: unknown, value: unknown): this {
      const state = draftState<MapDraftState>(this)
      const source = draftValue<Map<unknown, unknown>>(state)
      const wrapped = wrappedSource(state)
      const normalizedKey = resolveMapKey(state, source, wrapped, key)
      const currentValue = readGet(source, wrapped, normalizedKey)
      const insertedValue = insertedCollectionValue(state, value, mapExposure, false)

      if (
        state.context.isSameDraftValue(currentValue, insertedValue) &&
        (currentValue !== undefined || readHas(source, wrapped, normalizedKey))
      ) {
        // SameValue writes against existing entries do not mark a change.
        return this
      }

      const copy = prepareMapCopy(state)
      const copyKey = resolveMapKey(state, copy, false, normalizedKey)
      const present = builtinMapHas(copy, copyKey)
      const insertedKey = present
        ? copyKey
        : insertedCollectionValue(state, copyKey, mapExposure, true)
      builtinMapSet(copy, insertedKey, insertedValue)
      if (!present) state.members.revision += 1
      state.modified = true
      return this
    }
  }
  // `constructor` resolves to the source's class, as the draft's prototype chain does.
  Reflect.deleteProperty(DraftMap.prototype, 'constructor')
  return DraftMap
})()

/** Stores Map draft state; a working copy, when present, is a native Map. */
// fallow-ignore-next-line unused-type -- part of the declared type of builtinModules in builtins.ts
export interface MapDraftState extends BaseDraftState {
  readonly kind: typeof MAP_KIND
  /** The Vue lookup index of the keys; changing the keys bumps its revision. */
  readonly members: WrappedIndex
}
