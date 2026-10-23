import { edgeAt, snapshotValue, type SnapshotReceiver } from '../graph/edge'
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
import { collectionSurface, eachMember, normalize } from './shared/collection'
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
import {
  Detached,
  builtinSetDelete,
  builtinSetSize,
  builtinSetAdd,
  nativeSetValues,
} from '../standard-prototypes'

/** Stable global identity owned by the set module. */
export const SET_KIND = Symbol.for('@escapace/reconcile/set')

/** Walks a `Set` as the built-in iterator does. */
const setIterator: unknown = /* @__PURE__ */ (() =>
  Reflect.getOwnPropertyDescriptor(Set.prototype, Symbol.iterator)?.value)()
const setWalk = (set: object) =>
  builtinWalk(set as Set<unknown>, Set.prototype, setIterator, (collection) =>
    Set.prototype.values.call(collection as Set<unknown>),
  )

/** Whether the draft's object is an instance of a subclass of `Set`. */
const subclassed = (state: SetDraftState): boolean =>
  Object.getPrototypeOf(state.base) !== Set.prototype

/** The members as the draft holds them now, in a collection whose `has` is the built-in one, as
 * the built-in methods decide membership: a subclass's `has` does not. */
const liveMembers = (state: SetDraftState): Set<unknown> =>
  !subclassed(state) || state.copy !== undefined || vueState(state)
    ? draftValue<Set<unknown>>(state)
    : prepareSetCopy(state)

/** Whether the draft's object is Vue reactive state, read once per draft. */
function vueState(state: SetDraftState): boolean {
  return (state.members.vue ??= storageIdentity(state.base) !== state.base)
}

const setPolicySurface = /* @__PURE__ */ collectionSurface({
  builtin: {
    put: builtinSetAdd,
    remove: builtinSetDelete,
    size: builtinSetSize,
    iterator: (current) =>
      Reflect.apply(nativeSetValues as () => unknown, current, []) as Iterator<unknown>,
  },
  own: {
    iterator: (current) => (current as Set<unknown>).values(),
    put: (current, key) => {
      ;(current as Set<unknown>).add(key)
    },
    remove: (current, key) => {
      ;(current as Set<unknown>).delete(key)
    },
    size: (current) => (current as Set<unknown>).size,
  },
  width: 1,
  read: (entry) => entry,
})
const setPolicyWrite: NativePolicy<SetLayout>['freshWrite'] = (node, target, index, resolve) => {
  builtinSetAdd(target, resolve(node.edges[index]))
}
const setCapture = {
  construction: noValue,
  observe(value, begin, edge, mode) {
    const set = value as Set<unknown>
    const members = mode === 'snapshot' ? set.values() : set[Symbol.iterator]()
    begin({ kind: SET_KIND, prototype: Object.getPrototypeOf(set) as object | null })
    for (const child of members) edge(child)
  },
} satisfies CapturePolicy<SetLayout>

const setConstruction = {
  bindings: independentBindings,
  allocate: (node) => adoptPrototype(new Set<unknown>(), node.layout.prototype, Set.prototype),
} satisfies ConstructionPolicy<SetLayout>

// Adds one snapshot member to the receiving reference's target.
function writeSetMember(this: SnapshotReceiver, edge: Edge): void {
  builtinSetAdd(this.target!, snapshotValue(edge))
}

export const setSnapshot = /* @__PURE__ */ (() =>
  /* @__PURE__ */ freeze({
    ...setCapture,
    snapshot(layout, _resolve, writer) {
      writer.initialize(
        layout,
        adoptPrototype(new Set<unknown>(), layout.prototype, Set.prototype),
        writeSetMember,
      )
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
    observeDraft(source, observer) {
      const { base } = observer
      // The prototype is the base's, which a working copy keeps.
      const prototype = Object.getPrototypeOf(base ?? source) as object | null
      observer.begin({ kind: SET_KIND, prototype })
      for (const value of setWalk(source))
        observer.edge(
          value,
          undefined,
          isObject(value) && (base as Set<unknown> | undefined)?.has(value) === true,
        )
    },
    reuse(node, current, visit) {
      const set = current as Set<unknown>
      if (set.size !== node.edges.length) return false
      let index = 0
      return !eachMember(setWalk(set), (value) => !visit(value, edgeAt(node.edges, index++)))
    },
  } satisfies ImmutablePolicy<SetLayout>['immutable']),
  someChild(source, _read, test) {
    return eachMember(setWalk(source), test)
  },
}))() satisfies ImmutablePolicy<SetLayout>

const setPolicy = /* @__PURE__ */ (() => ({ ...setSnapshot, ...setPublication, ...setImmutable }))()

/** Identifies ordered Set payloads with one edge per member. */
// fallow-ignore-next-line unused-type -- part of the declared type of builtinModules in builtins.ts
export interface SetLayout {
  readonly kind: typeof SET_KIND
  /** The source's prototype, which a copy keeps. */
  readonly prototype: object | null
}

export const setExposure: Extract<ExposureFacet, { tag: 'collection' }> = /* @__PURE__ */ freeze({
  tag: 'collection',
  singleton: (value) => new Set([value]),
})

export const setDraft = /* @__PURE__ */ freeze({
  tag: 'structural',
  handle: (state): object => new DraftSet(state),
  state: (base, context) => ({
    base,
    context,
    copy: undefined,
    handle: undefined,
    kind: SET_KIND,
    members: { built: undefined, revision: 0, vue: undefined },
    modified: false,
    properties: undefined,
    source() {
      return this.copy ?? this.base
    },
  }),
}) satisfies DraftStrategy<SetDraftState>

const setRecognition = /* @__PURE__ */ freeze({
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

  // The working copy keeps the source's class, so a subclass's methods act on it as on the base.
  const base = state.base as Set<unknown>
  state.copy = adoptPrototype(
    new Set(setWalk(base)),
    Object.getPrototypeOf(base) as object,
    Set.prototype,
  )
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
  state: SetDraftState,
  source: Set<unknown>,
  value: unknown,
  index: WrappedIndex = state.members,
  // `has` resolves through the source's own `has`, as `has` on the draft does; the built-in methods
  // use the built-in one on the working copy.
  contains?: (value: unknown) => boolean,
): unknown {
  const holds = contains ?? ((form: unknown) => source.has(form))
  if (holds(value)) return value
  if (!isObject(value)) return LOOKUP_MISS
  const form = otherForm(state.context, value, holds)
  if (form !== LOOKUP_MISS) return form
  return (
    resolveWrappedCollectionMember(
      source,
      state.context.statesByIdentity.get(value)?.base ?? value,
      state.base,
      index,
      setWalk,
    ) ?? LOOKUP_MISS
  )
}

/**
 * The form of `value` that `holds` finds, or `LOOKUP_MISS`: the object a draft drafts or its
 * handle, or the original or the copy of a special value, which a read of a `Date`, buffer, view
 * or URL makes and which counts as its original, as a draft does.
 */
function otherForm(
  context: BaseDraftState['context'],
  value: object,
  holds: (value: unknown) => boolean,
): unknown {
  const drafted = context.statesByIdentity.get(value)
  if (drafted !== undefined) {
    const { base, handle } = drafted
    if (base !== value && holds(base)) return base
    if (handle !== undefined && holds(handle)) return handle
  }
  return copyForm(context, value, holds)
}

/** The original or the copy of a special value that `holds` finds, or `LOOKUP_MISS`. */
function copyForm(
  context: BaseDraftState['context'],
  value: object,
  holds: (value: unknown) => boolean,
): unknown {
  const form = context.copyBase(value) ?? context.copyOf(value)
  return form !== undefined && holds(form) ? form : LOOKUP_MISS
}

/** Resolves a member as the built-in methods do, with the built-in `has` on `members`. */
/** Resolves a member with the built-in `has` on `raw`, the raw object of `members`. */
const builtinHas = (
  state: SetDraftState,
  members: Set<unknown>,
  value: unknown,
  index: WrappedIndex | undefined,
  raw: object,
): unknown =>
  resolveSetMember(state, members, value, index, (member) => Set.prototype.has.call(raw, member))

const builtinMember = (
  state: SetDraftState,
  members: Set<unknown>,
  value: unknown,
  index?: WrappedIndex,
): unknown =>
  // Only a subclass instance has another `has`; `liveMembers` gives its working copy or, in Vue
  // reactive state, its proxy, whose raw object holds the members without making a copy.
  Object.getPrototypeOf(members) === Set.prototype
    ? resolveSetMember(state, members, value, index)
    : builtinHas(state, members, value, index, storageIdentity(members))

type SetMethod =
  | 'difference'
  | 'intersection'
  | 'isDisjointFrom'
  | 'isSubsetOf'
  | 'isSupersetOf'
  | 'symmetricDifference'
  | 'union'

/** A set-like operand as the native `Set` methods read it (`GetSetRecord`). */
interface SetRecord {
  readonly set: object
  readonly size: number
  readonly has: (this: unknown, value: unknown) => unknown
  readonly keys: (this: unknown) => unknown
}

const isObjectLike = (value: unknown): value is object =>
  isObject(value) || typeof value === 'function'

const nativeHas = (has: unknown): has is (value: unknown) => boolean =>
  has === Set.prototype.has || has === Map.prototype.has

/** Reads `size`, `has` and `keys` from a set-like operand, in the native order and with the
 * native errors. */
function setRecord(other: unknown): SetRecord {
  if (!isObjectLike(other)) throw new TypeError('The Set method operand is not an object')
  const number = +((other as { size: unknown }).size as number)
  if (Number.isNaN(number)) throw new TypeError('The Set method operand size is not a number')
  const size = Math.trunc(number)
  if (size < 0) throw new RangeError('The Set method operand size is negative')
  const has = (other as { has: unknown }).has
  if (typeof has !== 'function') throw new TypeError('The Set method operand has no has method')
  const keys = (other as { keys: unknown }).keys
  if (typeof keys !== 'function') throw new TypeError('The Set method operand has no keys method')
  return { has: has as SetRecord['has'], keys: keys as SetRecord['keys'], set: other, size }
}

const setSize = /* @__PURE__ */ (() =>
  Reflect.getOwnPropertyDescriptor(Set.prototype, 'size')!.get as (this: Set<unknown>) => number)()

/** The number of members, read as the native methods read it: not through a subclass's `size`. */
const sizeOf = (state: SetDraftState): number =>
  subclassed(state) ? setSize.call(prepareSetCopy(state)) : draftValue<Set<unknown>>(state).size

/** The members as they are now, read as the native methods read them: not through a subclass's
 * iterator. */
const membersOf = (state: SetDraftState): Set<unknown> =>
  subclassed(state)
    ? new Set(Set.prototype.values.call(prepareSetCopy(state)))
    : new Set(draftValue<Set<unknown>>(state))

/**
 * One `Set` method call on a draft: its operand and the lookups it builds at most once.
 *
 * @remarks
 * An operand whose `has` is the built-in one, directly or under a Vue reactive proxy, cannot
 * observe its calls, so it is asked for each form of a member; any other operand's `has` receives
 * the member as this draft gives it. The operand's Vue markers are read only when an object member
 * or key needs them.
 */
class SetCall extends Detached {
  // Declared and assigned in the constructor, as every internal class's fields are: a parameter
  // property or field initializer becomes a defineProperty call with the unrenamed name, which
  // the build's renamed reads would miss.
  declare private operand:
    { readonly set: object; readonly has: (value: unknown) => boolean } | undefined
  declare private operandVue: boolean | undefined
  declare readonly record: SetRecord
  declare private readonly snapshot: WrappedIndex
  declare readonly state: SetDraftState
  declare private readonly vue: boolean

  constructor(state: SetDraftState, record: SetRecord) {
    super()
    this.operand = undefined
    this.operandVue = undefined
    this.record = record
    this.snapshot = { built: undefined, revision: 0, vue: undefined }
    this.state = state
    this.vue = vueState(state)
  }

  /** Whether the operand is Vue reactive state, which counts a Vue proxy as its raw object. */
  private wrapped(): boolean {
    if (this.operandVue !== undefined) return this.operandVue
    const { has, set } = this.record
    if (nativeHas(has)) {
      this.operand = { has, set }
      return (this.operandVue = false)
    }
    const raw = storageIdentity(set)
    const rawHas = raw === set ? undefined : (Reflect.get(raw, 'has') as unknown)
    if (nativeHas(rawHas)) this.operand = { has: rawHas, set: raw }
    return (this.operandVue = raw !== set)
  }

  /** Whether the operand holds `member`. */
  inOperand(member: unknown): boolean {
    const { record, state } = this
    if (!isObject(member)) return Boolean(record.has.call(record.set, member))
    const vue = this.wrapped() || this.vue
    const { operand } = this
    if (operand === undefined)
      return Boolean(record.has.call(record.set, draftChild(state, member)))
    // The member, the object it drafts, its draft and, in Vue reactive state, its raw object.
    const drafted = state.context.statesByIdentity.get(member)
    const base = drafted?.base ?? member
    if (operand.has.call(operand.set, member) || operand.has.call(operand.set, base)) return true
    const handle = drafted?.handle
    if (handle !== undefined && operand.has.call(operand.set, handle)) return true
    if (
      copyForm(state.context, member, (form) => Boolean(operand.has.call(operand.set, form))) !==
      LOOKUP_MISS
    )
      return true
    return vue && operand.has.call(operand.set, storageIdentity(base))
  }

  /** The member of `members`, this draft's live members or a `snapshot` of them, that `value` is a
   * form of, or `LOOKUP_MISS`. A Vue reactive operand's keys count as their raw objects. */
  memberOf(members: Set<unknown>, value: unknown, snapshot: boolean): unknown {
    const index = snapshot ? this.snapshot : this.state.members
    const member = builtinMember(this.state, members, value, index)
    if (member !== LOOKUP_MISS || !isObject(value) || !this.wrapped()) return member
    return builtinMember(this.state, members, storageIdentity(value), index)
  }
}

/** The operand's key iterator (`GetIteratorFromMethod`). */
function openKeys(record: SetRecord): { iterator: object; next: unknown } {
  const iterator = record.keys.call(record.set)
  if (!isObjectLike(iterator))
    throw new TypeError('The Set method operand keys are not an iterator')
  return { iterator, next: (iterator as { next: unknown }).next }
}

/** Calls `visit` with each key, `-0` as `0`, until it returns false, and then closes the iterator
 * as the native methods do. Returns whether every key was visited. */
function everyKey(keys: { iterator: object; next: unknown }, visit: (key: unknown) => boolean) {
  for (;;) {
    const step = (keys.next as () => unknown).call(keys.iterator)
    if (!isObjectLike(step)) throw new TypeError('The Set method operand key step is not an object')
    // eslint-disable-next-line typescript/strict-boolean-expressions -- ToBoolean, as a native step reads done
    if ((step as { done: unknown }).done) return true
    const key = (step as { value: unknown }).value
    if (!visit(key === 0 ? 0 : key)) {
      closeKeys(keys.iterator)
      return false
    }
  }
}

/** Closes the operand's key iterator early, as `IteratorClose` does. */
function closeKeys(iterator: object): void {
  const close = (iterator as { return?: unknown }).return
  if (close === undefined || close === null) return
  if (typeof close !== 'function') throw new TypeError('The iterator return is not a method')
  if (!isObjectLike(close.call(iterator)))
    throw new TypeError('The iterator return result is not an object')
}

/** Walks this draft's members live, as the native methods do, until `visit` returns false. */
function everyMember(state: SetDraftState, visit: (member: unknown) => boolean): boolean {
  const members = Set.prototype.values.call(prepareSetCopy(state))
  for (let step = members.next(); step.done !== true; step = members.next())
    if (!visit(step.value)) return false
  return true
}

/** Each of `members` as this draft gives it. */
const drafted = (state: SetDraftState, members: Set<unknown>): Set<unknown> => {
  const result = new Set<unknown>()
  for (const member of Set.prototype.values.call(members)) result.add(draftChild(state, member))
  return result
}

/**
 * The native `Set` methods on a draft (DraftSetMethods).
 *
 * @remarks
 * Each follows the algorithm of the specification: it reads the operand's `size`, `has` and `keys`
 * once, chooses by the two sizes whether to walk this draft, live or as a copy as the method's
 * algorithm says, or the operand's keys, and stops where the algorithm stops. Membership in this draft is by member identity, as `has` decides it.
 * Members of this draft are given as their drafts and the operand's keys as the operand gives them.
 */
const setMethods: Record<SetMethod, (call: SetCall) => unknown> = {
  difference(call) {
    const { record, state } = call
    const members = membersOf(state)
    const result = drafted(state, members)
    // The spec walks its copy of the members, not the live set, so members the operand adds or
    // removes do not change which ones it asks about.
    if (sizeOf(state) <= record.size) {
      for (const member of members)
        if (call.inOperand(member)) result.delete(draftChild(state, member))
    } else
      everyKey(openKeys(record), (key) => {
        const member = call.memberOf(members, key, true)
        if (member !== LOOKUP_MISS) result.delete(draftChild(state, member))
        return true
      })
    return result
  },
  intersection(call) {
    const { record, state } = call
    const result = new Set<unknown>()
    if (sizeOf(state) <= record.size)
      everyMember(state, (member) => {
        if (call.inOperand(member)) result.add(draftChild(state, member))
        return true
      })
    else
      everyKey(openKeys(record), (key) => {
        const member = call.memberOf(liveMembers(state), key, false)
        if (member !== LOOKUP_MISS) result.add(draftChild(state, member))
        return true
      })
    return result
  },
  isDisjointFrom(call) {
    const { record, state } = call
    return sizeOf(state) <= record.size
      ? everyMember(state, (member) => !call.inOperand(member))
      : everyKey(
          openKeys(record),
          (key) => call.memberOf(liveMembers(state), key, false) === LOOKUP_MISS,
        )
  },
  isSubsetOf(call) {
    const { record, state } = call
    if (sizeOf(state) > record.size) return false
    return everyMember(state, (member) => call.inOperand(member))
  },
  isSupersetOf(call) {
    const { record, state } = call
    if (sizeOf(state) < record.size) return false
    return everyKey(
      openKeys(record),
      (key) => call.memberOf(liveMembers(state), key, false) !== LOOKUP_MISS,
    )
  },
  symmetricDifference(call) {
    const { state } = call
    return withEveryKey(call, (key, members, result) => {
      const member = call.memberOf(members, key, true)
      const value = member === LOOKUP_MISS ? key : draftChild(state, member)
      const present = result.has(value)
      if (call.memberOf(liveMembers(state), key, false) !== LOOKUP_MISS) {
        if (present) result.delete(value)
      } else if (!present) result.add(key)
    })
  },
  union(call) {
    return withEveryKey(call, (key, members, result) => {
      if (call.memberOf(members, key, true) === LOOKUP_MISS) result.add(key)
    })
  },
}

/**
 * Starts from this draft's members, as drafts, and calls `visit` with each of the operand's keys,
 * as `union` and `symmetricDifference` do: the key iterator is opened before the members are
 * copied, and `members` is that copy.
 */
function withEveryKey(
  call: SetCall,
  visit: (key: unknown, members: Set<unknown>, result: Set<unknown>) => void,
): Set<unknown> {
  const keys = openKeys(call.record)
  const members = membersOf(call.state)
  const result = drafted(call.state, members)
  everyKey(keys, (key) => {
    visit(key, members, result)
    return true
  })
  return result
}

/**
 * Runs a `Set` method: a subclass's own version on the working copy, as it runs on a native `Set`
 * of its class, otherwise the draft's.
 *
 * @remarks
 * A subclass's version can change the copy through `this`, so the draft counts as written, and
 * finalization keeps the original when the members end up equal. Returning the copy returns the
 * draft, and a plain `Set` it builds that holds members of this draft as stored objects is given as
 * a new `Set` that holds them as drafts.
 */
function setMethod(state: SetDraftState, method: SetMethod, other: unknown): unknown {
  const prototype = Object.getPrototypeOf(state.base) as object
  const own = prototype === Set.prototype ? undefined : (Reflect.get(prototype, method) as unknown)
  if (own === undefined || own === Set.prototype[method])
    return setMethods[method](new SetCall(state, setRecord(other)))
  const copy = prepareSetCopy(state)
  const result = (own as (other: unknown) => unknown).call(copy, other)
  state.members.revision += 1
  state.modified = true
  if (result === copy) return state.handle
  // A draft, a Vue reactive set or any other wrapper already gives what it holds as it holds it.
  if (
    !(result instanceof Set) ||
    storageIdentity(result) !== result ||
    state.context.statesByIdentity.get(result)?.handle === result
  )
    return result
  // Only a plain `Set` the override built, as `super.union` builds one, is given as drafts; a set of
  // its own class can hold state its constructor made, and the operand is returned as it is.
  if (Object.getPrototypeOf(result) !== Set.prototype || result === other) return result
  let changed = false
  const values: unknown[] = []
  const returned = setWalk(result as Set<unknown>)
  for (const value of returned) {
    const member = isObject(value) ? builtinMember(state, copy, value) : LOOKUP_MISS
    const given = member === LOOKUP_MISS ? value : draftChild(state, member)
    changed ||= given !== value
    values.push(given)
  }
  // The returned set is never changed: one that holds members of this draft as stored objects is
  // given as a new `Set` that holds them as drafts.
  return changed ? new Set(values) : result
}

/**
 * Provides copy-on-write Set operations with draft-aware membership resolution.
 *
 * @remarks
 * Reads and no-op mutations retain the base. Effective mutations copy before writing.
 * Iteration walks the working copy natively; held wrappers remain usable after recipe completion.
 * @internal
 */
const DraftSet = /* @__PURE__ */ (() => {
  class DraftSet extends draftCollectionBase(
    Set.prototype,
    prepareSetCopy as (state: BaseDraftState) => Set<unknown>,
    draftChild,
  ) {
    /** Binds the wrapper to its call-local draft state. */
    constructor(state: SetDraftState) {
      super(state)
      adoptDraftClass(this, DraftSet.prototype, Set.prototype, state)
      // A Set result carries only its members, so the draft refuses new properties.
      Object.preventExtensions(this)
    }

    /** Reads the current collection size without allocating a copy. */
    get size(): number {
      const state = draftState<SetDraftState>(this)
      return draftValue<Set<unknown>>(state).size
    }

    /** Walks the members, as the working copy's own iterator gives them, each object as its
     * draft. */
    [Symbol.iterator](): IterableIterator<unknown> {
      const state = draftState<SetDraftState>(this)
      return draftWalk(prepareSetCopy(state)[Symbol.iterator](), (member) =>
        draftChild(state, member),
      )
    }

    /** The members of this draft, then those of `other` it does not hold. */
    union(other: unknown): Set<unknown> {
      return setMethod(draftState<SetDraftState>(this), 'union', other) as Set<unknown>
    }

    /** The members also in `other`. */
    intersection(other: unknown): Set<unknown> {
      return setMethod(draftState<SetDraftState>(this), 'intersection', other) as Set<unknown>
    }

    /** The members not in `other`. */
    difference(other: unknown): Set<unknown> {
      return setMethod(draftState<SetDraftState>(this), 'difference', other) as Set<unknown>
    }

    /** The members of this draft not in `other`, then those of `other` not in this draft. */
    symmetricDifference(other: unknown): Set<unknown> {
      return setMethod(
        draftState<SetDraftState>(this),
        'symmetricDifference',
        other,
      ) as Set<unknown>
    }

    /** Whether every member is in `other`. */
    isSubsetOf(other: unknown): boolean {
      return setMethod(draftState<SetDraftState>(this), 'isSubsetOf', other) as boolean
    }

    /** Whether every member of `other` is in this draft. */
    isSupersetOf(other: unknown): boolean {
      return setMethod(draftState<SetDraftState>(this), 'isSupersetOf', other) as boolean
    }

    /** Whether no member is in `other`. */
    isDisjointFrom(other: unknown): boolean {
      return setMethod(draftState<SetDraftState>(this), 'isDisjointFrom', other) as boolean
    }

    /** Adds a member only when no equivalent member already exists. */
    add(value: unknown): this {
      const state = draftState<SetDraftState>(this)
      const source = liveMembers(state)

      if (builtinMember(state, source, value) !== LOOKUP_MISS) {
        // Duplicate add is a true no-op and does not mark the draft modified.
        return this
      }

      const insertedValue = insertedCollectionValue(state, value, setExposure, false)
      prepareSetCopy(state).add(insertedValue)
      state.members.revision += 1
      state.modified = true
      return this
    }

    /** Clears a nonempty working collection and records an effective change. */
    clear(): void {
      const state = draftState<SetDraftState>(this)
      const source = draftValue<Set<unknown>>(state)

      if (source.size === 0) {
        // Clearing an already-empty set is a true no-op and does not mark the draft modified.
        return
      }

      prepareSetCopy(state).clear()
      state.members.revision += 1
      state.modified = true
    }

    /** Deletes an existing Set member and records only a successful removal. */
    delete(value: unknown): boolean {
      const state = draftState<SetDraftState>(this)
      const source = draftValue<Set<unknown>>(state)
      const target = resolveSetMember(state, source, value)

      if (target === LOOKUP_MISS) {
        // Deleting a missing element is a true no-op and does not mark the draft modified.
        return false
      }

      const copy = prepareSetCopy(state)
      const removed = copy.delete(resolveSetMember(state, copy, target))
      // A subclass's `delete` can change the copy whatever it returns.
      if (removed || subclassed(state)) {
        state.members.revision += 1
        state.modified = true
      }
      return removed
    }

    /** Tests membership using draft-base and wrapper identity rules. */
    has(value: unknown): boolean {
      const state = draftState<SetDraftState>(this)
      const source = draftValue<Set<unknown>>(state)
      return resolveSetMember(state, source, value) !== LOOKUP_MISS
    }
  }
  // `constructor` resolves to the source's class, as the draft's prototype chain does.
  Reflect.deleteProperty(DraftSet.prototype, 'constructor')
  // A draft has a `Set` method exactly when the runtime's `Set` has it.
  for (const method of Object.keys(setMethods))
    if (!(method in Set.prototype)) Reflect.deleteProperty(DraftSet.prototype, method)
  return DraftSet
})()

/** Stores Set draft state; a working copy, when present, is a native Set. */
// fallow-ignore-next-line unused-type -- part of the declared type of builtinModules in builtins.ts
export interface SetDraftState extends BaseDraftState {
  readonly kind: typeof SET_KIND
  /** The Vue lookup index of the members; changing the members bumps its revision. */
  readonly members: WrappedIndex
}
