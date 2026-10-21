import { hasOwn, isObject } from '../../object-property'
import { normalizeCollectionInsertion, storageIdentity } from '../../adapters/vue'
import type { BaseDraftState, ExposureFacet } from '../../types'
import { defineData, isDataDescriptor } from '../../standard-prototypes'

/**
 * Reads a collection's current working value, using its base until a copy exists.
 *
 * @remarks
 * Object and array callers use their state's descriptor-aware reads instead.
 */
export function draftValue<T extends object>(state: BaseDraftState): T {
  return (state.copy ?? state.base) as T
}

export const PATCH_STATE_SYMBOL = /* @__PURE__ */ Symbol.for('@escapace/reconcile/patch')

// Supply draft identity information; the storage boundary owns collection policy.
export function insertedCollectionValue(
  state: BaseDraftState,
  value: unknown,
  exposure: Extract<ExposureFacet, { tag: 'collection' }>,
  unwrap: boolean,
): unknown {
  return normalizeCollectionInsertion(
    state.base,
    value,
    isObject(value) ? state.context.statesByIdentity.get(value)?.base : undefined,
    exposure,
    unwrap,
  )
}

/**
 * Builds the base of the `Map` or `Set` draft class.
 *
 * @remarks
 * Its prototype chain continues at the built-in's prototype, so a draft is an instance of the
 * built-in and inherits its `Symbol.toStringTag` (DraftClass.draft_instanceOf). `values`, `keys`,
 * `entries` and `forEach` call the same method of the working copy that `prepareCopy` returns, so a
 * subclass override runs where it runs natively, and give each value as `draftChild` does and each
 * key as `key` does.
 */
export function draftCollectionBase(
  builtin: object,
  prepareCopy: (state: BaseDraftState) => Map<unknown, unknown> | Set<unknown>,
  key: (state: BaseDraftState, key: unknown) => unknown,
) {
  abstract class DraftCollection {
    declare readonly [PATCH_STATE_SYMBOL]: BaseDraftState

    /** Walks the entries, each value as its draft. */
    entries(): IterableIterator<[unknown, unknown]> {
      const state = this[PATCH_STATE_SYMBOL]
      return draftWalk(prepareCopy(state).entries(), (entry: [unknown, unknown]) => [
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
      const state = this[PATCH_STATE_SYMBOL]
      prepareCopy(state).forEach((value: unknown, entryKey: unknown) => {
        callback.call(thisArgument, draftChild(state, value), key(state, entryKey), this)
      })
    }

    /** Walks the keys. */
    keys(): IterableIterator<unknown> {
      const state = this[PATCH_STATE_SYMBOL]
      return draftWalk(prepareCopy(state).keys(), (entryKey) => key(state, entryKey))
    }

    /** Walks the values, each object as its draft. */
    values(): IterableIterator<unknown> {
      const state = this[PATCH_STATE_SYMBOL]
      return draftWalk(prepareCopy(state).values(), (value) => draftChild(state, value))
    }
  }
  Object.setPrototypeOf(DraftCollection.prototype, builtin)
  Reflect.deleteProperty(DraftCollection.prototype, 'constructor')
  return DraftCollection
}

/** The value `key` holds on `value` or on `prototype`, its prototype, or that one's chain, read
 * without calling a getter. */
function inherited(value: object, prototype: object | null, key: PropertyKey): unknown {
  const own = Reflect.getOwnPropertyDescriptor(value, key)
  if (own !== undefined) return isDataDescriptor(own) ? own.value : undefined
  for (
    let owner = prototype;
    owner !== null;
    owner = Object.getPrototypeOf(owner) as object | null
  ) {
    const descriptor = Reflect.getOwnPropertyDescriptor(owner, key)
    if (descriptor !== undefined) return isDataDescriptor(descriptor) ? descriptor.value : undefined
  }
  return undefined
}

/**
 * Walks a `Map` or `Set` as the built-in constructors and methods walk it: with the built-in
 * iterator, `walk`, past a subclass's override of `Symbol.iterator`.
 *
 * @remarks
 * A built-in instance is walked as itself. So is a subclass instance whose iterator is the built-in
 * `iterator`, so a wrapper such as a proxy keeps working, and a Vue reactive proxy, whose iterator
 * forwards to its raw object.
 */
export function builtinWalk<T>(
  collection: Iterable<T>,
  builtin: object,
  iterator: unknown,
  walk: (collection: Iterable<T>) => Iterable<T>,
): Iterable<T> {
  const prototype = Object.getPrototypeOf(collection) as object | null
  // A built-in instance walks as itself, through its own iterator if it has one.
  if (prototype === builtin) return collection
  return inherited(collection, prototype, Symbol.iterator) === iterator ||
    storageIdentity(collection as object) !== collection
    ? collection
    : walk(collection)
}

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
export function draftWalk<T, R>(steps: Iterator<T>, project: (value: T) => R): IterableIterator<R> {
  const next = Reflect.get(steps, 'next') as (this: Iterator<T>) => IteratorResult<T>
  const prototype = Object.getPrototypeOf(steps) as object
  const native = nativeIterators.has(prototype)
  const walk = Object.create(native ? prototype : iteratorPrototype) as IterableIterator<R>
  const methods = {
    next: (): IteratorResult<R> => {
      const step = next.call(steps)
      // eslint-disable-next-line typescript/strict-boolean-expressions -- ToBoolean, as for...of reads done
      if (step.done) return step
      // eslint-disable-next-line perfectionist/sort-objects -- a native iterator result's key order
      return { value: project(step.value), done: false }
    },
    return: (value?: unknown): IteratorResult<R> =>
      (Reflect.get(steps, 'return') as (value?: unknown) => IteratorResult<R>).call(steps, value),
  }
  defineData(walk, 'next', methods.next, false)
  if (!native && Reflect.get(steps, 'return') !== undefined)
    defineData(walk, 'return', methods.return, false)
  return walk
}

/**
 * Gives a draft its source's class.
 *
 * @remarks
 * A draft of a built-in instance already has it. A draft of a subclass instance gets a call-local
 * layer that holds the draft's collection methods over the subclass's prototype, so methods the
 * subclass adds and `instanceof` resolve as on the source, and collection methods resolve to the
 * draft's (DraftClass.lookup_other, DraftClass.lookup_method); they act on the original, then on a
 * working copy of the same class, through its own methods, so a subclass override still runs. The
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
    const descriptors: PropertyDescriptorMap = {}
    for (let owner = layer; owner !== builtin; owner = Object.getPrototypeOf(owner) as object)
      for (const key of Reflect.ownKeys(owner))
        if (!hasOwn(descriptors, key))
          (descriptors as Record<PropertyKey, PropertyDescriptor>)[key] =
            Object.getOwnPropertyDescriptor(owner, key)!
    subclassLayer = Object.create(prototype, descriptors) as object
    layers.set(prototype, subclassLayer)
  }
  Object.setPrototypeOf(draft, subclassLayer)
}
