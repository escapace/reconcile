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
import { resolveWrappedCollectionMember, type WrappedIndex } from '../adapters/vue'
import type { BaseDraftState, Edge, ExposureFacet, NativePolicy } from '../types'
import { defineType } from './registry'
import { collectionSurface, eachEntry, eachOpenedEntry, normalize } from './shared/collection'
import {
  insertedCollectionValue,
  draftState,
  draftValue,
  adoptDraftClass,
  draftChild,
  draftCollectionBase,
  draftWalk,
  builtinWalk,
} from './shared/draft-collection'
import { emptyEdges } from './shared/empty'

/** Stable global identity owned by the map module. */
export const MAP_KIND = Symbol.for('@escapace/reconcile/map')

/** Walks a `Map` as the built-in iterator does. */
const mapIterator: unknown = /* @__PURE__ */ (() =>
  Reflect.getOwnPropertyDescriptor(Map.prototype, Symbol.iterator)?.value)()
const mapWalk = (map: Map<unknown, unknown>) =>
  builtinWalk(map, Map.prototype, mapIterator, (collection) =>
    Map.prototype.entries.call(collection as Map<unknown, unknown>),
  )

/** The keys of a `Map`, walked as the built-in iterator does. */
function mapKeys(map: object): unknown[] {
  const keys: unknown[] = []
  eachEntry(mapWalk(map as Map<unknown, unknown>), (key) => keys.push(key) < 0)
  return keys
}

const mapPolicySurface = /* @__PURE__ */ collectionSurface({
  width: 2,
  iterator: (current) => (current as Map<unknown, unknown>).entries(),
  read: (entry, slot, strict) =>
    strict ? (entry as unknown[])[slot] : (entry as unknown[] | undefined)?.[slot],
  replace(edges, current, resolve) {
    const map = current as Map<unknown, unknown>
    map.clear()
    for (let index = 0; index < edges.length; index += 2)
      map.set(resolve(edges[index]), resolve(edges[index + 1]))
  },
  size: (current) => (current as Map<unknown, unknown>).size,
})
const mapPolicyWrite: NativePolicy<MapLayout>['freshWrite'] = (node, target, index, resolve) => {
  if (index % 2 === 1)
    (target as Map<unknown, unknown>).set(
      resolve(node.edges[index - 1]),
      resolve(node.edges[index]),
    )
}
const mapCapture = {
  construction: noValue,
  observe(value, begin, edge, mode) {
    const map = value as Map<unknown, unknown>
    const method = (map as unknown as Record<PropertyKey, unknown>)[
      mode === 'snapshot' ? 'entries' : Symbol.iterator
    ]
    const entries: unknown = Reflect.apply(method as () => unknown, map, [])
    begin({ kind: MAP_KIND, prototype: Object.getPrototypeOf(map) as object | null })
    eachOpenedEntry(entries, method, (key, child) => {
      edge(key)
      edge(child)
      return false
    })
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
          target.set(resolve(pending), resolve(edge))
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
      const map = base as Map<unknown, unknown> | undefined
      eachEntry(mapWalk(source as Map<unknown, unknown>), (key, value) => {
        const present = map?.has(key) === true
        observer.edge(key, undefined, present)
        observer.edge(
          value,
          undefined,
          present && map !== undefined && Object.is(value, map.get(key)),
        )
        return false
      })
    },
    reuse(node, current, visit) {
      const map = current as Map<unknown, unknown>
      if (map.size * 2 !== node.edges.length) return false
      let index = 0
      return !eachEntry(
        mapWalk(map),
        (key, value) =>
          !visit(key, edgeAt(node.edges, index++)) || !visit(value, edgeAt(node.edges, index++)),
      )
    },
  } satisfies ImmutablePolicy<MapLayout>['immutable']),
  someChild(source, _read, test) {
    return eachEntry(
      mapWalk(source as Map<unknown, unknown>),
      (key, value) => test(key) || test(value),
    )
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

/**
 * Captures a native Map once, preserving iterator order and key normalization.
 */
function prepareMapCopy(state: MapDraftState): Map<unknown, unknown> {
  if (state.copy !== undefined) {
    return state.copy as Map<unknown, unknown>
  }

  // The working copy keeps the source's class, so a subclass's methods act on it as on the base.
  const base = state.base as Map<unknown, unknown>
  state.copy = adoptPrototype(
    new Map(mapWalk(base)),
    Object.getPrototypeOf(base) as object,
    Map.prototype,
  )
  return state.copy as Map<unknown, unknown>
}

/**
 * Resolves a Map key through its stored identity, draft base, handle, and wrapper equivalence.
 *
 * @returns An existing key when found, otherwise the normalized key for insertion.
 */
function resolveMapKey(state: MapDraftState, source: Map<unknown, unknown>, key: unknown): unknown {
  const { base, context } = state
  // Newly assigned maps may store handles, while existing maps normally store bases.
  if (!isObject(key) || source.has(key)) {
    return key
  }

  const drafted = context.statesByIdentity.get(key)
  if (drafted !== undefined) {
    if (drafted.base !== key && source.has(drafted.base)) return drafted.base
    const handle = drafted.handle
    if (handle !== undefined && source.has(handle)) return handle
    key = drafted.base
  }
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
      return draftValue<Map<unknown, unknown>>(state).size
    }

    /** Walks the entries, as the working copy's own iterator gives them, each value as its draft. */
    [Symbol.iterator](): IterableIterator<[unknown, unknown]> {
      const state = draftState<MapDraftState>(this)
      return draftWalk(prepareMapCopy(state)[Symbol.iterator](), (entry: [unknown, unknown]) => [
        entry[0],
        draftChild(state, entry[1]),
      ])
    }

    /** Clears a nonempty working collection and records an effective change. */
    clear(): void {
      const state = draftState<MapDraftState>(this)
      const source = draftValue<Map<unknown, unknown>>(state)

      if (source.size === 0) {
        // Clearing an already-empty map is a true no-op and does not mark the draft modified.
        return
      }

      prepareMapCopy(state).clear()
      state.members.revision += 1
      state.modified = true
    }

    /** Deletes an existing Map entry after resolving its identity in the captured copy. */
    delete(key: unknown): boolean {
      const state = draftState<MapDraftState>(this)
      const source = draftValue<Map<unknown, unknown>>(state)
      const normalizedKey = resolveMapKey(state, source, key)

      if (!source.has(normalizedKey)) {
        // Deleting a missing key is a true no-op and does not mark the draft modified.
        return false
      }

      const copy = prepareMapCopy(state)
      const copyKey = resolveMapKey(state, copy, normalizedKey)
      copy.delete(copyKey)
      state.members.revision += 1
      state.modified = true
      return true
    }

    /** Returns a draft-safe Map value while preserving missing-key behavior. */
    get(key: unknown): unknown {
      const state = draftState<MapDraftState>(this)
      const source = draftValue<Map<unknown, unknown>>(state)
      const normalizedKey = resolveMapKey(state, source, key)
      const value = source.get(normalizedKey)

      if (value === undefined && !source.has(normalizedKey)) {
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
      return source.has(resolveMapKey(state, source, key))
    }

    /** Stores a value unless the resolved entry already represents the same draft value. */
    set(key: unknown, value: unknown): this {
      const state = draftState<MapDraftState>(this)
      const source = draftValue<Map<unknown, unknown>>(state)
      const normalizedKey = resolveMapKey(state, source, key)
      const currentValue = source.get(normalizedKey)
      const insertedValue = insertedCollectionValue(state, value, mapExposure, false)

      if (
        state.context.isSameDraftValue(currentValue, insertedValue) &&
        (currentValue !== undefined || source.has(normalizedKey))
      ) {
        // SameValue writes against existing entries do not mark a change.
        return this
      }

      const copy = prepareMapCopy(state)
      const copyKey = resolveMapKey(state, copy, normalizedKey)
      const present = copy.has(copyKey)
      const insertedKey = present
        ? copyKey
        : insertedCollectionValue(state, copyKey, mapExposure, true)
      copy.set(insertedKey, insertedValue)
      // A subclass's `set` can change other keys of the copy.
      if (!present || Object.getPrototypeOf(state.base) !== Map.prototype)
        state.members.revision += 1
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
