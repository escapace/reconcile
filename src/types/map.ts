import { freeze, independentBindings, yes } from './shared/empty'
import { noValue } from './shared/empty'
import type {
  CapturePolicy,
  ConstructionPolicy,
  DraftContext,
  DraftStrategy,
  ImmutablePolicy,
  PublicationPolicy,
  Recognition,
  SnapshotPolicy,
} from '../types'
import { isObject } from '../object-property'
import { resolveWrappedCollectionMember } from '../adapters/vue'
import type { BaseDraftState, Edge, ExposureFacet, NativePolicy } from '../types'
import { defineType } from './registry'
import { collectionSurface, normalize } from './shared/collection'
import {
  insertedCollectionValue,
  PATCH_STATE_SYMBOL,
  draftValue,
  UnsupportedDraftCollectionIteration,
} from './shared/draft-collection'
import { emptyEdges } from './shared/empty'

/** Stable global identity owned by the map module. */
export const MAP_KIND = Symbol.for('@escapace/reconcile/map')

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
    begin({ kind: MAP_KIND })
    const map = value as Map<unknown, unknown>
    for (const [key, child] of mode === 'snapshot' ? map.entries() : map) {
      edge(key)
      edge(child)
    }
  },
} satisfies CapturePolicy<MapLayout>

const mapConstruction = {
  bindings: independentBindings,
  allocate: () => new Map<unknown, unknown>(),
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
      const target = new Map<unknown, unknown>()
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
    observeDraft(source, begin, edge, { base }) {
      begin({ kind: MAP_KIND })
      const map = base as Map<unknown, unknown> | undefined
      for (const [key, value] of source as Map<unknown, unknown>) {
        const present = map?.has(key) === true
        edge(key, undefined, present)
        edge(value, undefined, present && map !== undefined && Object.is(value, map.get(key)))
      }
    },
    reuse(node, current, visit) {
      const map = current as Map<unknown, unknown>
      if (map.size * 2 !== node.edges.length) return false
      let index = 0
      for (const [key, value] of map)
        if (
          !visit(key, node.edges[index++] ?? { value: undefined }) ||
          !visit(value, node.edges[index++] ?? { value: undefined })
        )
          return false
      return true
    },
  } satisfies ImmutablePolicy<MapLayout>['immutable']),
  someChild(source, _read, test) {
    for (const [key, value] of source as Map<unknown, unknown>)
      if (test(key) || test(value)) return true
    return false
  },
}))() satisfies ImmutablePolicy<MapLayout>

const mapPolicy = /* @__PURE__ */ (() => ({ ...mapSnapshot, ...mapPublication, ...mapImmutable }))()

/** Identifies ordered Map payloads whose edges alternate keys and values. */
// fallow-ignore-next-line unused-type -- part of the declared type of builtinModules in builtins.ts
export interface MapLayout {
  readonly kind: typeof MAP_KIND
}

export const mapExposure: Extract<ExposureFacet, { tag: 'collection' }> = /* @__PURE__ */ freeze({
  tag: 'collection',
  singleton: (value) => new Map([[value, undefined]]),
})

export const mapDraft = /* @__PURE__ */ freeze({
  tag: 'structural',
  handle: (state) => new DraftMap(state),
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

export const mapRecognition = /* @__PURE__ */ freeze({
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

  state.copy = new Map(state.base as Map<unknown, unknown>)
  return state.copy as Map<unknown, unknown>
}

/**
 * Resolves a Map key through its stored identity, draft base, handle, and wrapper equivalence.
 *
 * @returns An existing key when found, otherwise the normalized key for insertion.
 */
function resolveMapKey(
  context: DraftContext,
  source: Map<unknown, unknown>,
  key: unknown,
  base: object,
): unknown {
  // Newly assigned maps may store handles, while existing maps normally store bases.
  if (!isObject(key) || source.has(key)) {
    return key
  }

  const state = context.statesByIdentity.get(key)
  if (state !== undefined) {
    if (state.base !== key && source.has(state.base)) return state.base
    const handle = state.handle
    if (handle !== undefined && source.has(handle)) return handle
    key = state.base
  }
  return resolveWrappedCollectionMember(source, key as object, base) ?? key
}

/**
 * Provides copy-on-write Map operations with draft-safe values and key resolution.
 *
 * @remarks
 * Reads and no-op mutations retain the base. Effective mutations copy before writing.
 * Collection iteration is unsupported; held wrappers remain usable after recipe completion.
 * @internal
 */
const DraftMap = /* @__PURE__ */ (() =>
  class DraftMap extends UnsupportedDraftCollectionIteration {
    declare readonly [PATCH_STATE_SYMBOL]: MapDraftState

    /** Binds the wrapper to its call-local draft state. */
    constructor(state: MapDraftState) {
      super()
      this[PATCH_STATE_SYMBOL] = state
    }

    /** Reads the current collection size without allocating a copy. */
    get size(): number {
      const state = this[PATCH_STATE_SYMBOL]
      return draftValue<Map<unknown, unknown>>(state).size
    }

    /** Clears a nonempty working collection and records an effective change. */
    clear(): void {
      const state = this[PATCH_STATE_SYMBOL]
      const source = draftValue<Map<unknown, unknown>>(state)

      if (source.size === 0) {
        // Clearing an already-empty map is a true no-op and does not mark the draft modified.
        return
      }

      prepareMapCopy(state).clear()
      state.modified = true
    }

    /** Deletes an existing Map entry after resolving its identity in the captured copy. */
    delete(key: unknown): boolean {
      const state = this[PATCH_STATE_SYMBOL]
      const source = draftValue<Map<unknown, unknown>>(state)
      const normalizedKey = resolveMapKey(state.context, source, key, state.base)

      if (!source.has(normalizedKey)) {
        // Deleting a missing key is a true no-op and does not mark the draft modified.
        return false
      }

      const copy = prepareMapCopy(state)
      const copyKey = resolveMapKey(state.context, copy, normalizedKey, state.base)
      copy.delete(copyKey)
      state.modified = true
      return true
    }

    /** Returns a draft-safe Map value while preserving missing-key behavior. */
    get(key: unknown): unknown {
      const state = this[PATCH_STATE_SYMBOL]
      const source = draftValue<Map<unknown, unknown>>(state)
      const normalizedKey = resolveMapKey(state.context, source, key, state.base)
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
      const state = this[PATCH_STATE_SYMBOL]
      const source = draftValue<Map<unknown, unknown>>(state)
      return source.has(resolveMapKey(state.context, source, key, state.base))
    }

    /** Stores a value unless the resolved entry already represents the same draft value. */
    set(key: unknown, value: unknown): this {
      const state = this[PATCH_STATE_SYMBOL]
      const source = draftValue<Map<unknown, unknown>>(state)
      const normalizedKey = resolveMapKey(state.context, source, key, state.base)
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
      const copyKey = resolveMapKey(state.context, copy, normalizedKey, state.base)
      const insertedKey = copy.has(copyKey)
        ? copyKey
        : insertedCollectionValue(state, copyKey, mapExposure, true)
      copy.set(insertedKey, insertedValue)
      state.modified = true
      return this
    }
  })()

/** Stores Map draft state; a working copy, when present, is a native Map. */
// fallow-ignore-next-line unused-type -- part of the declared type of builtinModules in builtins.ts
export interface MapDraftState extends BaseDraftState {
  readonly kind: typeof MAP_KIND
}
