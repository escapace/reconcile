import { edgeAt } from '../graph/edge'
import { adoptPrototype } from './shared/prototype'
import { freeze, independentBindings } from './shared/empty'
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
import type { BaseDraftState, Edge, NativePolicy } from '../types'
import { defineType } from './registry'
import { collectionSurface, normalize } from './shared/collection'
import {
  draftState,
  draftValue,
  adoptDraftClass,
  draftChild,
  draftCollectionBase,
  draftWalk,
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
  eachBuiltinEntry,
  forEachBuiltinEntry,
  mapStep,
  openBuiltin,
  openMapEntries,
} from '../standard-prototypes'

/** Stable global identity owned by the map module. */
export const MAP_KIND = Symbol.for('@escapace/reconcile/map')

const mapPolicySurface = /* @__PURE__ */ collectionSurface({
  builtin: {
    open: openMapEntries,
    put: builtinMapSet,
    remove: builtinMapDelete,
    size: builtinMapSize,
    step: mapStep,
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
    begin({ kind: MAP_KIND, prototype })
    forEachBuiltinEntry(value, (child, key) => {
      edge(key)
      edge(child)
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
     * Resolve both edges when the value arrives, not when the key first arrives, so a pair is
     * written once, after the live image of both edges exists.
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
      // The source is the base or, when it differs, the draft's working copy, a built-in `Map`.
      forEachBuiltinEntry(source, (value, key) => {
        const present = base !== undefined && builtinMapHas(base, key)
        observer.edge(key, undefined, present)
        observer.edge(value, undefined, present && Object.is(value, builtinMapGet(base, key)))
      })
    },
    reuse(node, current, visit) {
      if (builtinMapSize(current) * 2 !== node.edges.length) return false
      let index = 0
      return !eachBuiltinEntry(
        current,
        (key, value) =>
          !visit(key, edgeAt(node.edges, index++)) || !visit(value, edgeAt(node.edges, index++)),
      )
    },
  } satisfies ImmutablePolicy<MapLayout>['immutable']),
  someChild(source, _read, test) {
    return eachBuiltinEntry(source, (key, value) => test(key) || test(value))
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

export const mapDraft = /* @__PURE__ */ freeze({
  tag: 'structural',
  handle: (state): object => new DraftMap(state),
  state: (base, context) => ({
    base,
    context,
    copy: undefined,
    handle: undefined,
    kind: MAP_KIND,
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

  // The working copy keeps the source's class, so methods a subclass adds act on it as on the base;
  // it is filled, and later read and written, with the built-ins.
  const base = state.base as Map<unknown, unknown>
  const copy = new Map<unknown, unknown>()
  forEachBuiltinEntry(base, (value, key) => {
    builtinMapSet(copy, key, value)
  })
  state.copy = adoptPrototype(copy, Object.getPrototypeOf(base) as object, Map.prototype)
  return state.copy as Map<unknown, unknown>
}

/**
 * Resolves a Map key through its stored identity, draft base and handle.
 *
 * @returns An existing key when found, otherwise the normalized key for insertion.
 */
function resolveMapKey(state: MapDraftState, source: Map<unknown, unknown>, key: unknown): unknown {
  const { context } = state
  // Newly assigned maps may store handles, while existing maps normally store bases.
  if (!isObject(key) || builtinMapHas(source, key)) {
    return key
  }

  const drafted = context.statesByIdentity.get(key)
  if (drafted !== undefined) {
    const form = draftedForm(drafted, key, source, builtinMapHas)
    if (form !== undefined) return form
    key = drafted.base
  }
  // A copy that a read of a `Date`, buffer, view or URL made counts as its original, as a draft does.
  const copied = context.copyBase(key as object) ?? context.copyOf(key as object)
  if (copied !== undefined && builtinMapHas(source, copied)) return copied
  return key
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
      return builtinMapSize(draftValue(draftState<MapDraftState>(this)))
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

      if (builtinMapSize(draftValue(state)) === 0) {
        // Clearing an already-empty map is a true no-op and does not mark the draft modified.
        return
      }

      builtinMapClear(prepareMapCopy(state))
      state.modified = true
    }

    /** Deletes an existing Map entry after resolving its identity in the captured copy. */
    delete(key: unknown): boolean {
      const state = draftState<MapDraftState>(this)
      const source = draftValue<Map<unknown, unknown>>(state)
      const normalizedKey = resolveMapKey(state, source, key)

      if (!builtinMapHas(source, normalizedKey)) {
        // Deleting a missing key is a true no-op and does not mark the draft modified.
        return false
      }

      const copy = prepareMapCopy(state)
      builtinMapDelete(copy, resolveMapKey(state, copy, normalizedKey))
      state.modified = true
      return true
    }

    /** Returns a draft-safe Map value while preserving missing-key behavior. */
    get(key: unknown): unknown {
      const state = draftState<MapDraftState>(this)
      const source = draftValue<Map<unknown, unknown>>(state)
      const normalizedKey = resolveMapKey(state, source, key)
      const value = builtinMapGet(source, normalizedKey)

      if (value === undefined && !builtinMapHas(source, normalizedKey)) {
        return undefined
      }

      if (!isObject(value)) {
        return value
      }

      return state.context.materializeChild(value)
    }

    /** Tests membership using draft-base identity rules. */
    has(key: unknown): boolean {
      const state = draftState<MapDraftState>(this)
      const source = draftValue<Map<unknown, unknown>>(state)
      return builtinMapHas(source, resolveMapKey(state, source, key))
    }

    /** Stores a value unless the resolved entry already represents the same draft value. */
    set(key: unknown, value: unknown): this {
      const state = draftState<MapDraftState>(this)
      const source = draftValue<Map<unknown, unknown>>(state)
      const normalizedKey = resolveMapKey(state, source, key)
      const currentValue = builtinMapGet(source, normalizedKey)

      if (
        state.context.isSameDraftValue(currentValue, value) &&
        (currentValue !== undefined || builtinMapHas(source, normalizedKey))
      ) {
        // SameValue writes against existing entries do not mark a change.
        return this
      }

      const copy = prepareMapCopy(state)
      builtinMapSet(copy, resolveMapKey(state, copy, normalizedKey), value)
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
}
