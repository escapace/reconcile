import { hasOwn, isObject } from '../../object-property'
import { normalizeCollectionInsertion, storageIdentity } from '../../adapters/vue'
import type { BaseDraftState, ExposureFacet } from '../../types'
import {
  defineData,
  eachBuiltinEntry,
  eachBuiltinMember,
  forEachBuiltinEntry,
  forEachBuiltinMember,
  openBuiltin,
} from '../../standard-prototypes'
import { eachEntry, eachMember } from './collection'

/**
 * Reads a collection's current working value, using its base until a copy exists.
 *
 * @remarks
 * Object and array callers use their state's descriptor-aware reads instead.
 */
export function draftValue<T extends object>(state: BaseDraftState): T {
  return (state.copy ?? state.base) as T
}

/**
 * Holds a collection draft's call-local state in a private field, so reflection, spreading and
 * accessors on the prototype chain never see it: a draft has the own properties of its source.
 * The draft classes discard this class's prototype from their chain; the field stays.
 */
class DraftStateHolder {
  readonly #state: BaseDraftState

  constructor(state: BaseDraftState) {
    this.#state = state
  }

  /** The state of a draft this module constructed. */
  static of<S extends BaseDraftState>(draft: object): S {
    return (draft as DraftStateHolder).#state as S
  }
}

/** The call-local state of a `Map` or `Set` draft. */
export const draftState = <S extends BaseDraftState>(draft: object): S =>
  DraftStateHolder.of<S>(draft)

// Supply draft identity information; the storage boundary owns collection policy. An object that
// is neither a draft nor a Vue proxy, and that the collection's raw storage does not already hold
// (`held`), is one the recipe adds: it is stored as itself, a read gives its draft, which a Vue
// proxy of it shares, and the result holds it, with the drafts it holds finalized, as it holds any
// object the recipe adds. An object the collection held is stored as Vue exposes it.
export function insertedCollectionValue(
  state: BaseDraftState,
  value: unknown,
  exposure: Extract<ExposureFacet, { tag: 'collection' }>,
  unwrap: boolean,
  held?: (raw: object, value: object) => boolean,
): unknown {
  if (!isObject(value)) return value
  const resolved = state.context.statesByIdentity.get(value)?.base
  if (
    resolved === undefined &&
    storageIdentity(value) === value &&
    held?.(storageIdentity(state.base), value) !== true
  )
    return value
  return normalizeCollectionInsertion(state.base, value, resolved, exposure, unwrap)
}

/** The walks every `Map` and `Set` draft inherits. */
export interface DraftCollectionWalks {
  entries: () => IterableIterator<[unknown, unknown]>
  forEach: (
    callback: (value: unknown, key: unknown, collection: unknown) => void,
    ...[thisArgument]: unknown[]
  ) => void
  keys: () => IterableIterator<unknown>
  values: () => IterableIterator<unknown>
}

/**
 * Builds the base of the `Map` or `Set` draft class.
 *
 * @remarks
 * Its prototype chain continues at the built-in's prototype, so a draft is an instance of the
 * built-in and inherits its `Symbol.toStringTag` (DraftClass.draft_instanceOf). `values`, `keys`,
 * `entries` and `forEach` walk the working copy that `prepareCopy` returns with the built-in
 * iterator, so no override runs, and give each value as `draftChild` does and each key as `key`
 * does.
 */
export function draftCollectionBase(
  builtin: object,
  prepareCopy: (state: BaseDraftState) => Map<unknown, unknown> | Set<unknown>,
  key: (state: BaseDraftState, key: unknown) => unknown,
): abstract new (state: BaseDraftState) => DraftCollectionWalks {
  const map = builtin === Map.prototype
  const open = (state: BaseDraftState, walk: 'entries' | 'keys' | 'values') =>
    openBuiltin(prepareCopy(state), map, walk)
  const walked = <R>(
    state: BaseDraftState,
    walk: 'entries' | 'keys' | 'values',
    project: (value: never) => R,
  ): IterableIterator<R> => {
    const opened = open(state, walk)
    return draftWalk(opened.iterator as Iterator<never>, project, opened.step)
  }
  abstract class DraftCollection extends DraftStateHolder {
    /** Walks the entries, each value as its draft. */
    entries(): IterableIterator<[unknown, unknown]> {
      const state = draftState(this)
      return walked(state, 'entries', (entry: [unknown, unknown]) => [
        key(state, entry[0]),
        draftChild(state, entry[1]),
      ])
    }

    /** Calls `callback` with each value, its key and this draft, in walk order. */
    forEach(
      callback: (value: unknown, key: unknown, collection: unknown) => void,
      ...[thisArgument]: unknown[]
    ): void {
      if (typeof callback !== 'function')
        throw new TypeError('The forEach callback is not a function')
      const state = draftState(this)
      const opened = open(state, 'entries')
      for (;;) {
        const step = opened.step(opened.iterator) as IteratorResult<[unknown, unknown]>
        if (step.done === true) return
        Reflect.apply(callback, thisArgument, [
          draftChild(state, step.value[1]),
          key(state, step.value[0]),
          this,
        ])
      }
    }

    /** Walks the keys. */
    keys(): IterableIterator<unknown> {
      const state = draftState(this)
      return walked(state, 'keys', (entryKey: unknown) => key(state, entryKey))
    }

    /** Walks the values, each object as its draft. */
    values(): IterableIterator<unknown> {
      const state = draftState(this)
      return walked(state, 'values', (value: unknown) => draftChild(state, value))
    }
  }
  Object.setPrototypeOf(DraftCollection.prototype, builtin)
  Reflect.deleteProperty(DraftCollection.prototype, 'constructor')
  return DraftCollection
}

/**
 * Whether a `Map` or `Set` is a wrapper, such as a Vue reactive proxy, which holds no contents of
 * its own: it is read and written through its own methods. Every other collection, including an
 * instance of a subclass, is read and written with the built-ins, so no override runs.
 */
export const wrappedCollection = (collection: object, prototype?: object | null): boolean =>
  storageIdentity(collection, prototype) !== collection

/**
 * Calls `each` with the value and key of every entry of a `Map`, in order: through its own
 * iterator when it is a wrapper, otherwise with the built-in `forEach`.
 */
export function forEachMapEntry(
  map: object,
  each: (value: unknown, key: unknown) => void,
  wrapped: boolean,
): void {
  if (!wrapped) forEachBuiltinEntry(map, each)
  else
    eachEntry(map as Iterable<unknown>, (key, value) => {
      each(value, key)
      return false
    })
}

/**
 * Calls `each` with every member of a `Set`, in order: through its own iterator when it is a
 * wrapper, otherwise with the built-in `forEach`.
 */
export function forEachSetMember(
  set: object,
  each: (member: unknown) => void,
  wrapped: boolean,
): void {
  if (!wrapped) forEachBuiltinMember(set, each)
  else
    eachMember(set as Iterable<unknown>, (member) => {
      each(member)
      return false
    })
}

/** Calls `each` with each entry of a `Map` until it returns true; returns whether it did. */
export const eachMapEntry = (
  map: object,
  each: (key: unknown, value: unknown) => boolean,
  wrapped: boolean = wrappedCollection(map),
): boolean => (wrapped ? eachEntry(map as Iterable<unknown>, each) : eachBuiltinEntry(map, each))

/** Calls `each` with each member of a `Set` until it returns true; returns whether it did. */
export const eachSetMember = (
  set: object,
  each: (member: unknown) => boolean,
  wrapped: boolean = wrappedCollection(set),
): boolean => (wrapped ? eachMember(set as Iterable<unknown>, each) : eachBuiltinMember(set, each))

/** A value a draft yields: an object as its draft, as a read returns it. */
export const draftChild = (state: BaseDraftState, value: unknown): unknown =>
  isObject(value) ? state.context.materializeChild(value) : value

/** The prototypes of native `Map` and `Set` iterators. */
const nativeIterators: ReadonlySet<unknown> = /* @__PURE__ */ (() =>
  new Set([
    Object.getPrototypeOf(new Map().entries()),
    Object.getPrototypeOf(new Set().values()),
  ]))()
const iteratorPrototype = /* @__PURE__ */ (() =>
  Object.getPrototypeOf(Object.getPrototypeOf([][Symbol.iterator]())) as object)()

/**
 * Walks an iterator over a draft's working copy, giving each value through `project`.
 *
 * @remarks
 * Making the working copy is not a change, and every later write through the draft changes that
 * same copy, so the walk sees writes as a native iteration does (DraftIteration.iterate_kept,
 * DraftIteration.write_after_iterate). The walk is a native iterator's own kind: over a native
 * iterator it has that iterator's prototype and, like it, no `return`, so leaving a loop early
 * does not end it; over a subclass's iterator it forwards `return`.
 */
export function draftWalk<T, R>(
  steps: Iterator<T>,
  project: (value: T) => R,
  // The built-in step of a native iterator, read when the module loads, called with the iterator.
  builtinStep?: (iterator: object) => IteratorResult<unknown>,
): IterableIterator<R> {
  const next = (builtinStep === undefined ? Reflect.get(steps, 'next') : undefined) as (
    this: Iterator<T>,
  ) => IteratorResult<T>
  const prototype = Object.getPrototypeOf(steps) as object
  const native = nativeIterators.has(prototype)
  const result = Object.create(native ? prototype : iteratorPrototype) as IterableIterator<R>
  const methods = {
    next: (): IteratorResult<R> => {
      const step =
        builtinStep === undefined
          ? Reflect.apply(next, steps, [])
          : (builtinStep(steps) as IteratorResult<T>)
      // eslint-disable-next-line typescript/strict-boolean-expressions -- ToBoolean, as for...of reads done
      if (step.done) return step
      // eslint-disable-next-line perfectionist/sort-objects -- a native iterator result's key order
      return { value: project(step.value), done: false }
    },
    return: (value?: unknown): IteratorResult<R> =>
      Reflect.apply(Reflect.get(steps, 'return') as (value?: unknown) => IteratorResult<R>, steps, [
        value,
      ]),
  }
  defineData(result, 'next', methods.next, false)
  if (!native && Reflect.get(steps, 'return') !== undefined)
    defineData(result, 'return', methods.return, false)
  return result
}

/**
 * Gives a draft its source's class.
 *
 * @remarks
 * A draft of a built-in instance already has it. A draft of a subclass instance gets a call-local
 * layer that holds the draft's collection methods over the subclass's prototype, so methods the
 * subclass adds and `instanceof` resolve as on the source, and collection methods resolve to the
 * draft's (DraftClass.lookup_other, DraftClass.lookup_method); they act on the original, then on a
 * working copy of the same class, with the built-in methods, so an override never runs. The
 * class's own `constructor` is removed, so `constructor` also resolves as on the source.
 */
export function adoptDraftClass(
  draft: object,
  layer: object,
  builtin: object,
  state: BaseDraftState,
): void {
  const prototype = Object.getPrototypeOf(state.base) as object
  if (prototype === builtin) return
  const layers = (state.context.draftLayers ??= new Map<object, object>())
  let subclassLayer: object | undefined = layers.get(prototype)
  if (subclassLayer === undefined) {
    const copy = Object.create(prototype) as object
    // Each descriptor inherits nothing, so what `Object.prototype` holds under a descriptor field
    // such as `get` or `value` is not read as part of it; the nearest layer defines each key.
    for (let owner = layer; owner !== builtin; owner = Object.getPrototypeOf(owner) as object) {
      const keys = Reflect.ownKeys(owner)
      for (let index = 0; index < keys.length; index += 1)
        if (!hasOwn(copy, keys[index]))
          Reflect.defineProperty(
            copy,
            keys[index],
            Object.setPrototypeOf(
              Object.getOwnPropertyDescriptor(owner, keys[index])!,
              null,
            ) as PropertyDescriptor,
          )
    }
    subclassLayer = copy
    layers.set(prototype, subclassLayer)
  }
  Object.setPrototypeOf(draft, subclassLayer)
}
