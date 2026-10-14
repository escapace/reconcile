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
import type { BaseDraftState, ExposureFacet, NativePolicy } from '../types'
import { defineType } from './registry'
import { collectionSurface, normalize } from './shared/collection'
import {
  insertedCollectionValue,
  PATCH_STATE_SYMBOL,
  draftValue,
  UnsupportedDraftCollectionIteration,
} from './shared/draft-collection'
import { emptyEdges } from './shared/empty'

/** Stable global identity owned by the set module. */
export const SET_KIND = Symbol.for('@escapace/reconcile/set')

const setPolicySurface = /* @__PURE__ */ collectionSurface({
  width: 1,
  iterator: (current) => (current as Set<unknown>).values(),
  read: (entry) => entry,
  replace(edges, current, resolve) {
    const set = current as Set<unknown>
    set.clear()
    for (const edge of edges) set.add(resolve(edge))
  },
  size: (current) => (current as Set<unknown>).size,
})
const setPolicyWrite: NativePolicy<SetLayout>['freshWrite'] = (node, target, index, resolve) => {
  ;(target as Set<unknown>).add(resolve(node.edges[index]))
}
const setCapture = {
  construction: noValue,
  observe(value, begin, edge, mode) {
    begin({ kind: SET_KIND })
    const set = value as Set<unknown>
    for (const child of mode === 'snapshot' ? set.values() : set) edge(child)
  },
} satisfies CapturePolicy<SetLayout>

const setConstruction = {
  bindings: independentBindings,
  allocate: () => new Set<unknown>(),
} satisfies ConstructionPolicy<SetLayout>

export const setSnapshot = /* @__PURE__ */ (() =>
  /* @__PURE__ */ freeze({
    ...setCapture,
    snapshot(layout, resolve, writer) {
      const target = new Set<unknown>()
      writer.initialize(layout, target, (edge) => {
        target.add(resolve(edge))
      })
    },
  }))() satisfies SnapshotPolicy<SetLayout>

export const setPublication = /* @__PURE__ */ (() =>
  /* @__PURE__ */ freeze({
    ...setCapture,
    ...setConstruction,
    ...setPolicySurface,
    compatible: yes,
    requirements: emptyEdges,
    seal: (node) => ({ ...node, edges: normalize(node.edges, 1) }),
  }))() satisfies PublicationPolicy<SetLayout>

export const setImmutable = /* @__PURE__ */ (() => ({
  ...setConstruction,
  freshWrite: setPolicyWrite,
  immutable: /* @__PURE__ */ freeze({
    tag: 'structural',
    observeDraft(source, begin, edge, { base }) {
      begin({ kind: SET_KIND })
      for (const value of source as Set<unknown>)
        edge(
          value,
          undefined,
          isObject(value) && (base as Set<unknown> | undefined)?.has(value) === true,
        )
    },
    reuse(node, current, visit) {
      const set = current as Set<unknown>
      if (set.size !== node.edges.length) return false
      let index = 0
      for (const value of set)
        if (!visit(value, node.edges[index++] ?? { value: undefined })) return false
      return true
    },
  } satisfies ImmutablePolicy<SetLayout>['immutable']),
  someChild(source, _read, test) {
    for (const value of source as Set<unknown>) if (test(value)) return true
    return false
  },
}))() satisfies ImmutablePolicy<SetLayout>

const setPolicy = /* @__PURE__ */ (() => ({ ...setSnapshot, ...setPublication, ...setImmutable }))()

/** Identifies ordered Set payloads with one edge per member. */
// fallow-ignore-next-line unused-type -- part of the declared type of builtinModules in builtins.ts
export interface SetLayout {
  readonly kind: typeof SET_KIND
}

export const setExposure: Extract<ExposureFacet, { tag: 'collection' }> = /* @__PURE__ */ freeze({
  tag: 'collection',
  singleton: (value) => new Set([value]),
})

export const setDraft = /* @__PURE__ */ freeze({
  tag: 'structural',
  handle: (state) => new DraftSet(state),
  state: (base, context) => ({
    base,
    context,
    copy: undefined,
    handle: undefined,
    kind: SET_KIND,
    modified: false,
    properties: undefined,
    source() {
      return this.copy ?? this.base
    },
  }),
}) satisfies DraftStrategy<SetDraftState>

export const setRecognition = /* @__PURE__ */ freeze({
  tag: 'predicate',
  test: (value: object) => value instanceof Set,
}) satisfies Recognition

export const setType = /* @__PURE__ */ defineType<SetLayout, SetDraftState>({
  draft: setDraft,
  exposure: setExposure,
  kind: SET_KIND,
  name: 'set',
  policy: setPolicy,
  recognition: setRecognition,
})

const LOOKUP_MISS = {}
/**
 * Captures a native Set once, preserving iterator order and membership normalization.
 */
function prepareSetCopy(state: SetDraftState): Set<unknown> {
  if (state.copy !== undefined) {
    return state.copy as Set<unknown>
  }

  state.copy = new Set(state.base as Set<unknown>)
  return state.copy as Set<unknown>
}

/**
 * Resolves Set membership through stored identities and recognized wrapper equivalence.
 *
 * @remarks
 * The miss sentinel distinguishes absence from a stored `undefined`. Keep this result contract
 * separate from Map key resolution, which also supplies keys for insertion.
 */
function resolveSetMember(
  context: DraftContext,
  source: Set<unknown>,
  value: unknown,
  base: object,
): unknown {
  if (source.has(value)) {
    return value
  }

  if (!isObject(value)) {
    return LOOKUP_MISS
  }

  const state = context.statesByIdentity.get(value)
  if (state !== undefined) {
    if (state.base !== value && source.has(state.base)) return state.base
    const handle = state.handle
    if (handle !== undefined && source.has(handle)) return handle
    value = state.base
  }

  return resolveWrappedCollectionMember(source, value as object, base) ?? LOOKUP_MISS
}

/**
 * Provides copy-on-write Set operations with draft-aware membership resolution.
 *
 * @remarks
 * Reads and no-op mutations retain the base. Effective mutations copy before writing.
 * Collection iteration is unsupported; held wrappers remain usable after recipe completion.
 * @internal
 */
const DraftSet = /* @__PURE__ */ (() =>
  class DraftSet extends UnsupportedDraftCollectionIteration {
    declare readonly [PATCH_STATE_SYMBOL]: SetDraftState

    /** Binds the wrapper to its call-local draft state. */
    constructor(state: SetDraftState) {
      super()
      this[PATCH_STATE_SYMBOL] = state
    }

    /** Reads the current collection size without allocating a copy. */
    get size(): number {
      const state = this[PATCH_STATE_SYMBOL]
      return draftValue<Set<unknown>>(state).size
    }

    /** Adds a member only when no equivalent member already exists. */
    add(value: unknown): this {
      const state = this[PATCH_STATE_SYMBOL]
      const source = draftValue<Set<unknown>>(state)

      if (resolveSetMember(state.context, source, value, state.base) !== LOOKUP_MISS) {
        // Duplicate add is a true no-op and does not mark the draft modified.
        return this
      }

      const insertedValue = insertedCollectionValue(state, value, setExposure, false)
      prepareSetCopy(state).add(insertedValue)
      state.modified = true
      return this
    }

    /** Clears a nonempty working collection and records an effective change. */
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

    /** Deletes an existing Set member and records only a successful removal. */
    delete(value: unknown): boolean {
      const state = this[PATCH_STATE_SYMBOL]
      const source = draftValue<Set<unknown>>(state)
      const target = resolveSetMember(state.context, source, value, state.base)

      if (target === LOOKUP_MISS) {
        // Deleting a missing element is a true no-op and does not mark the draft modified.
        return false
      }

      const copy = prepareSetCopy(state)
      const removed = copy.delete(resolveSetMember(state.context, copy, target, state.base))
      if (removed) {
        state.modified = true
      }
      return removed
    }

    /** Tests membership using draft-base and wrapper identity rules. */
    has(value: unknown): boolean {
      const state = this[PATCH_STATE_SYMBOL]
      const source = draftValue<Set<unknown>>(state)
      return resolveSetMember(state.context, source, value, state.base) !== LOOKUP_MISS
    }
  })()

/** Stores Set draft state; a working copy, when present, is a native Set. */
// fallow-ignore-next-line unused-type -- part of the declared type of builtinModules in builtins.ts
export interface SetDraftState extends BaseDraftState {
  readonly kind: typeof SET_KIND
}
