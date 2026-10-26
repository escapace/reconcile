import { adoptPrototype } from './shared/prototype'
import { freeze, independentBindings } from './shared/empty'
import { noValue } from './shared/empty'
import type {
  CapturePolicy,
  ConstructionPolicy,
  ImmutablePolicy,
  PublicationPolicy,
} from '../types'
import { isObject, knownPrototype } from '../object-property'
import type { BaseDraftState } from '../types'
import {
  collectionSurface,
  entriesMatch,
  normalize,
  type CollectionAccess,
} from './shared/collection'
import {
  draftState,
  draftValue,
  collectionDraft,
  draftChild,
  draftCollectionBase,
  draftWalk,
} from './shared/draft-collection'
import { emptyEdges } from './shared/empty'
import { copiedForm, draftedForm } from './shared/draft-members'
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

/** The `Map` kind. */
export const MAP_KIND = Symbol('map')

const mapAccess: CollectionAccess = {
  open: openMapEntries,
  put: builtinMapSet,
  remove: builtinMapDelete,
  size: builtinMapSize,
  step: mapStep,
  width: 2,
  read: (entry, slot) => (entry as unknown[] | undefined)?.[slot],
}
const mapPolicySurface = /* @__PURE__ */ collectionSurface(mapAccess)
const mapCapture = {
  construction: noValue,
  observe(value, begin, edge, _mode, known) {
    const prototype = knownPrototype(value, known)
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

export const mapPublication = /* @__PURE__ */ (() =>
  /* @__PURE__ */ freeze({
    ...mapCapture,
    ...mapConstruction,
    ...mapPolicySurface,
    requirements: emptyEdges,
    seal: (node) => ({ ...node, edges: normalize(node.edges, 2) }),
  }))() satisfies PublicationPolicy<MapLayout>

export const mapImmutable = /* @__PURE__ */ (() => ({
  immutable: /* @__PURE__ */ freeze({
    allocate: mapConstruction.allocate,
    tag: 'structural',
    // A new `Map` that holds one object as two keys, as when two keys share one special copy,
    // has fewer entries than its node: no plan that copies it can be built.
    fill(node, target, resolve) {
      const edges = node.edges
      for (let index = 1; index < edges.length; index += 2)
        builtinMapSet(target, resolve(edges[index - 1]), resolve(edges[index]))
      return builtinMapSize(target) * 2 === edges.length
    },
    observeDraft(source, observer) {
      const { base } = observer
      // The prototype is the base's, which a working copy keeps.
      const prototype = Object.getPrototypeOf(base ?? source) as object | null
      observer.begin({ kind: MAP_KIND, prototype })
      // The source is the base or, when it differs, the draft's working copy, a built-in `Map`.
      forEachBuiltinEntry(source, (value, key) => {
        const present = base !== undefined && observer.copies() && builtinMapHas(base, key)
        observer.edge(key, undefined, present)
        observer.edge(value, undefined, present && Object.is(value, builtinMapGet(base, key)))
      })
    },
    reuse: (node, current, visit) => entriesMatch(mapAccess, node.edges, current, visit),
  } satisfies ImmutablePolicy<MapLayout>['immutable']),
  someChild(source, _read, test) {
    return eachBuiltinEntry(source, (key, value) => test(key) || test(value))
  },
}))() satisfies ImmutablePolicy<MapLayout>

/** Identifies ordered Map payloads whose edges alternate keys and values. */
export interface MapLayout {
  readonly kind: typeof MAP_KIND
  /** The source's prototype, which a copy keeps. */
  readonly prototype: object | null
}

export const mapDraft = /* @__PURE__ */ collectionDraft<MapDraftState>(
  MAP_KIND,
  (state, prototype): object => new DraftMap(state, prototype),
)

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
  return copiedForm(context, key as object, source, builtinMapHas) ?? key
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

    /** Deletes an existing Map entry; the copy holds the source's keys, so the key resolved
     * against the source names it there too. */
    delete(key: unknown): boolean {
      const state = draftState<MapDraftState>(this)
      const source = draftValue<Map<unknown, unknown>>(state)
      const normalizedKey = resolveMapKey(state, source, key)

      if (!builtinMapHas(source, normalizedKey)) {
        // Deleting a missing key is a true no-op and does not mark the draft modified.
        return false
      }

      builtinMapDelete(prepareMapCopy(state), normalizedKey)
      state.modified = true
      return true
    }

    /** Returns a draft-safe Map value while preserving missing-key behavior. */
    get(key: unknown): unknown {
      const state = draftState<MapDraftState>(this)
      const source = draftValue<Map<unknown, unknown>>(state)
      const normalizedKey = resolveMapKey(state, source, key)
      const value = builtinMapGet(source, normalizedKey)

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

      // The copy holds the source's keys, so the key resolved against the source names its entry.
      builtinMapSet(prepareMapCopy(state), normalizedKey, value)
      state.modified = true
      return this
    }
  }
  // `constructor` resolves to the source's class, as the draft's prototype chain does.
  Reflect.deleteProperty(DraftMap.prototype, 'constructor')
  return DraftMap
})()

/** Stores Map draft state; a working copy, when present, is a native Map. */
export interface MapDraftState extends BaseDraftState {
  readonly kind: typeof MAP_KIND
}
