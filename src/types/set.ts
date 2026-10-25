import { adoptPrototype } from './shared/prototype'
import { freeze, independentBindings } from './shared/empty'
import { noValue } from './shared/empty'
import type {
  CapturePolicy,
  ConstructionPolicy,
  ImmutablePolicy,
  PublicationPolicy,
} from '../types'
import { isObject } from '../object-property'
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
  closeIterator,
  Detached,
  builtinSetAdd,
  builtinSetClear,
  builtinSetDelete,
  builtinSetHas,
  builtinSetSize,
  eachBuiltinMember,
  forEachBuiltinMember,
  openBuiltin,
  openSetValues,
  setStep,
} from '../standard-prototypes'

/** Stable global identity owned by the set module. */
export const SET_KIND = Symbol.for('@escapace/reconcile/set')

/** The members as the draft holds them now: its working copy, or its object until it has one. */
const liveMembers = (state: SetDraftState): Set<unknown> => draftValue<Set<unknown>>(state)

/** A native `Set` or `Map` operand and its `has`. */
interface SetOperand {
  readonly set: object
  readonly has: (value: unknown) => boolean
}
/** Whether a native operand holds `value`, asked through its own `has`. */
const operandHas = (operand: SetOperand, value: unknown): boolean =>
  Boolean(Reflect.apply(operand.has, operand.set, [value]))

const setAccess: CollectionAccess = {
  open: openSetValues,
  put: builtinSetAdd,
  remove: builtinSetDelete,
  size: builtinSetSize,
  step: setStep,
  width: 1,
  read: (entry) => entry,
}
const setPolicySurface = /* @__PURE__ */ collectionSurface(setAccess)
const setCapture = {
  construction: noValue,
  observe(value, begin, edge) {
    const prototype = Object.getPrototypeOf(value) as object | null
    begin({ kind: SET_KIND, prototype })
    forEachBuiltinMember(value, (child) => {
      edge(child)
    })
  },
} satisfies CapturePolicy<SetLayout>

const setConstruction = {
  bindings: independentBindings,
  allocate: (node) => adoptPrototype(new Set<unknown>(), node.layout.prototype, Set.prototype),
} satisfies ConstructionPolicy<SetLayout>

export const setPublication = /* @__PURE__ */ (() =>
  /* @__PURE__ */ freeze({
    ...setCapture,
    ...setConstruction,
    ...setPolicySurface,
    requirements: emptyEdges,
    seal: (node) => ({ ...node, edges: normalize(node.edges, 1) }),
  }))() satisfies PublicationPolicy<SetLayout>

export const setImmutable = /* @__PURE__ */ (() => ({
  immutable: /* @__PURE__ */ freeze({
    allocate: setConstruction.allocate,
    tag: 'structural',
    // A new `Set` that holds one object as two members has fewer members than its node.
    fill(node, target, resolve) {
      const edges = node.edges
      for (let index = 0; index < edges.length; index += 1)
        builtinSetAdd(target, resolve(edges[index]))
      return builtinSetSize(target) === edges.length
    },
    observeDraft(source, observer) {
      const { base } = observer
      // The prototype is the base's, which a working copy keeps.
      const prototype = Object.getPrototypeOf(base ?? source) as object | null
      observer.begin({ kind: SET_KIND, prototype })
      const set = base as Set<unknown> | undefined
      // The source is the base or, when it differs, the draft's working copy, a built-in `Set`.
      forEachBuiltinMember(source, (value) => {
        observer.edge(
          value,
          undefined,
          isObject(value) && set !== undefined && builtinSetHas(set, value),
        )
      })
    },
    reuse: (node, current, visit) => entriesMatch(setAccess, node.edges, current, visit),
  } satisfies ImmutablePolicy<SetLayout>['immutable']),
  someChild(source, _read, test) {
    return eachBuiltinMember(source, test)
  },
}))() satisfies ImmutablePolicy<SetLayout>

/** Identifies ordered Set payloads with one edge per member. */
export interface SetLayout {
  readonly kind: typeof SET_KIND
  /** The source's prototype, which a copy keeps. */
  readonly prototype: object | null
}

export const setDraft = /* @__PURE__ */ collectionDraft<SetDraftState>(
  SET_KIND,
  (state, prototype): object => new DraftSet(state, prototype),
)

const LOOKUP_MISS = {}
/**
 * Captures a native Set once, preserving iterator order and membership normalization.
 */
function prepareSetCopy(state: SetDraftState): Set<unknown> {
  if (state.copy !== undefined) {
    return state.copy as Set<unknown>
  }

  // The working copy keeps the source's class, so methods a subclass adds act on it as on the base;
  // it is filled, and later read and written, with the built-ins.
  const base = state.base as Set<unknown>
  const copy = new Set<unknown>()
  forEachBuiltinMember(base, (member) => {
    builtinSetAdd(copy, member)
  })
  state.copy = adoptPrototype(copy, Object.getPrototypeOf(base) as object, Set.prototype)
  return state.copy as Set<unknown>
}

/**
 * Resolves Set membership through stored identities.
 *
 * @remarks
 * The miss sentinel distinguishes absence from a stored `undefined`. Keep this result contract
 * separate from Map key resolution, which also supplies keys for insertion.
 */
function resolveSetMember(state: SetDraftState, source: Set<unknown>, value: unknown): unknown {
  if (builtinSetHas(source, value)) return value
  if (!isObject(value)) return LOOKUP_MISS
  return otherForm(state.context, value, source)
}

/**
 * The form of `value` that `set` holds, or `LOOKUP_MISS`: the object a draft drafts or its handle,
 * or the original or the copy of a special value, which a read of a `Date`, buffer, view or URL
 * makes and which counts as its original, as a draft does.
 */
function otherForm(context: BaseDraftState['context'], value: object, set: object): unknown {
  const drafted = context.statesByIdentity.get(value)
  if (drafted !== undefined) {
    const form = draftedForm(drafted, value, set, builtinSetHas)
    if (form !== undefined) return form
  }
  return copiedForm(context, value, set, builtinSetHas) ?? LOOKUP_MISS
}

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

/** The number of members now. */
const sizeOf = (state: SetDraftState): number => builtinSetSize(liveMembers(state))

/** A copy of the members as they are now, in order. */
const membersOf = (state: SetDraftState): Set<unknown> => {
  const members = new Set<unknown>()
  forEachBuiltinMember(liveMembers(state), (member) => {
    builtinSetAdd(members, member)
  })
  return members
}

/**
 * One `Set` method call on a draft: its operand and the lookups it builds at most once.
 *
 * @remarks
 * An operand whose `has` is the built-in one cannot observe its calls, so it is asked for each
 * form of a member; any other operand's `has` receives the member as this draft gives it.
 */
class SetCall extends Detached {
  // Declared and assigned in the constructor, as every internal class's fields are: a parameter
  // property or field initializer becomes a defineProperty call with the unrenamed name, which
  // the build's renamed reads would miss.
  declare private readonly operand: SetOperand | undefined
  declare readonly record: SetRecord
  declare readonly state: SetDraftState

  constructor(state: SetDraftState, record: SetRecord) {
    super()
    const { has, set } = record
    this.operand = nativeHas(has) ? { has, set } : undefined
    this.record = record
    this.state = state
  }

  /** Whether the operand holds `member`. */
  inOperand(member: unknown): boolean {
    const { operand, record, state } = this
    if (!isObject(member)) return Boolean(Reflect.apply(record.has, record.set, [member]))
    if (operand === undefined)
      return Boolean(Reflect.apply(record.has, record.set, [draftChild(state, member)]))
    // The member and the forms of the object it drafts.
    if (operandHas(operand, member)) return true
    const drafted = state.context.statesByIdentity.get(member)
    if (drafted !== undefined && draftedForm(drafted, member, operand, operandHas) !== undefined)
      return true
    return copiedForm(state.context, member, operand, operandHas) !== undefined
  }

  /** The member of `members`, this draft's live members or a copy of them, that `value` is a form
   * of, or `LOOKUP_MISS`. */
  memberOf(members: Set<unknown>, value: unknown): unknown {
    return resolveSetMember(this.state, members, value)
  }
}

/** The operand's key iterator (`GetIteratorFromMethod`). */
function openKeys(record: SetRecord): { iterator: object; next: unknown } {
  const iterator: unknown = Reflect.apply(record.keys, record.set, [])
  if (!isObjectLike(iterator))
    throw new TypeError('The Set method operand keys are not an iterator')
  return { iterator, next: (iterator as { next: unknown }).next }
}

/** Calls `visit` with each key, `-0` as `0`, until it returns false, and then closes the iterator
 * as the native methods do. Returns whether every key was visited. */
function everyKey(keys: { iterator: object; next: unknown }, visit: (key: unknown) => boolean) {
  for (;;) {
    const step: unknown = Reflect.apply(keys.next as () => unknown, keys.iterator, [])
    if (!isObjectLike(step)) throw new TypeError('The Set method operand key step is not an object')
    // eslint-disable-next-line typescript/strict-boolean-expressions -- ToBoolean, as a native step reads done
    if ((step as { done: unknown }).done) return true
    const key = (step as { value: unknown }).value
    if (!visit(key === 0 ? 0 : key)) {
      closeIterator(keys.iterator)
      return false
    }
  }
}

/** Walks this draft's members live, as the native methods do, until `visit` returns false. */
function everyMember(state: SetDraftState, visit: (member: unknown) => boolean): boolean {
  return !eachBuiltinMember(prepareSetCopy(state), (member) => !visit(member))
}

/** Each of `members` as this draft gives it. */
const drafted = (state: SetDraftState, members: Set<unknown>): Set<unknown> => {
  const result = new Set<unknown>()
  eachBuiltinMember(members, (member) => {
    builtinSetAdd(result, draftChild(state, member))
    return false
  })
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
      eachBuiltinMember(members, (member) => {
        if (call.inOperand(member)) builtinSetDelete(result, draftChild(state, member))
        return false
      })
    } else
      everyKey(openKeys(record), (key) => {
        const member = call.memberOf(members, key)
        if (member !== LOOKUP_MISS) builtinSetDelete(result, draftChild(state, member))
        return true
      })
    return result
  },
  intersection(call) {
    const { record, state } = call
    const result = new Set<unknown>()
    if (sizeOf(state) <= record.size)
      everyMember(state, (member) => {
        if (call.inOperand(member)) builtinSetAdd(result, draftChild(state, member))
        return true
      })
    else
      everyKey(openKeys(record), (key) => {
        const member = call.memberOf(liveMembers(state), key)
        if (member !== LOOKUP_MISS) builtinSetAdd(result, draftChild(state, member))
        return true
      })
    return result
  },
  isDisjointFrom(call) {
    const { record, state } = call
    return sizeOf(state) <= record.size
      ? everyMember(state, (member) => !call.inOperand(member))
      : everyKey(openKeys(record), (key) => call.memberOf(liveMembers(state), key) === LOOKUP_MISS)
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
      (key) => call.memberOf(liveMembers(state), key) !== LOOKUP_MISS,
    )
  },
  symmetricDifference(call) {
    const { state } = call
    return withEveryKey(call, (key, members, result) => {
      const member = call.memberOf(members, key)
      const value = member === LOOKUP_MISS ? key : draftChild(state, member)
      const present = builtinSetHas(result, value)
      if (call.memberOf(liveMembers(state), key) !== LOOKUP_MISS) {
        if (present) builtinSetDelete(result, value)
      } else if (!present) builtinSetAdd(result, key)
    })
  },
  union(call) {
    return withEveryKey(call, (key, members, result) => {
      if (call.memberOf(members, key) === LOOKUP_MISS) builtinSetAdd(result, key)
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
 * Runs a `Set` method of the draft: the native algorithm over the draft's members, even when the
 * draft's class overrides the method, as for every other collection method.
 */
const setMethod = (state: SetDraftState, method: SetMethod, other: unknown): unknown =>
  setMethods[method](new SetCall(state, setRecord(other)))

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
    /** Reads the current collection size without allocating a copy. */
    get size(): number {
      return sizeOf(draftState<SetDraftState>(this))
    }

    /** Walks the members of the working copy, each object as its draft. */
    [Symbol.iterator](): IterableIterator<unknown> {
      const state = draftState<SetDraftState>(this)
      const opened = openBuiltin(prepareSetCopy(state), false, 'values')
      return draftWalk(
        opened.iterator as Iterator<unknown>,
        (member) => draftChild(state, member),
        opened.step,
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

      if (resolveSetMember(state, source, value) !== LOOKUP_MISS) {
        // Duplicate add is a true no-op and does not mark the draft modified.
        return this
      }

      builtinSetAdd(prepareSetCopy(state), value)
      state.modified = true
      return this
    }

    /** Clears a nonempty working collection and records an effective change. */
    clear(): void {
      const state = draftState<SetDraftState>(this)

      if (sizeOf(state) === 0) {
        // Clearing an already-empty set is a true no-op and does not mark the draft modified.
        return
      }

      builtinSetClear(prepareSetCopy(state))
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

      // The copy holds the source's members, so the member found in the source is one of them.
      builtinSetDelete(prepareSetCopy(state), target)
      state.modified = true
      return true
    }

    /** Tests membership using draft-base identity rules. */
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
export interface SetDraftState extends BaseDraftState {
  readonly kind: typeof SET_KIND
}
