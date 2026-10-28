import { atomValue, isNode } from './graph/edge'
import { noValue } from './types/shared/empty'
import { isObject } from './object-property'
import { recognizeStructure } from './adapters/recognition'
import { atomPrototype, hiddenNames, prototypeOf } from './object-property'
import type { Edge, Layout, Primitive, PrototypeRead } from './types'
import { snapshotTypes } from './types/builtins'
import { setOwnProperty, standardPrototype } from './set-own-property'
import {
  builtinMapSet,
  builtinSetAdd,
  forEachBuiltinEntry,
  forEachBuiltinMember,
} from './standard-prototypes'
import { adoptPrototype } from './types/shared/prototype'
import { OBJECT_KIND } from './types/object'
import { ARRAY_KIND } from './types/array'
import { MAP_KIND } from './types/map'
import { SET_KIND } from './types/set'
import { DATE_KIND, timeOf } from './types/date'
import { ARRAY_BUFFER_KIND } from './types/array-buffer'
import { TYPED_ARRAY_KIND } from './types/typed-array'
import { DATA_VIEW_KIND } from './types/data-view'
import {
  copyBuffer,
  copyDataView,
  copyTypedArray,
  copyTypedFirst,
  bufferWith,
  typedBufferOf,
  viewElement,
} from './types/shared/binary-native'
import { Detached, defineData, hasElement } from './standard-prototypes'

// Read once: `key in Object.prototype` decides each new object's write.
const objectPrototype = /* @__PURE__ */ (() => Object.prototype)()

/**
 * The canonical traversal reference of one copied object: its copy, set before the copy enters
 * the public memo, and the layout of a value its kind's facet copied. A buffer first met through a
 * typed array copied from itself holds that array's copy instead, whose buffer is its copy.
 */
class SnapshotReference extends Detached {
  declare layout: Layout | undefined
  declare readonly node: number
  declare target: object | undefined
  declare view: ArrayBufferView | undefined

  constructor(node: number) {
    super()
    this.node = node
    this.layout = undefined
    this.target = undefined
    this.view = undefined
  }
}

/**
 * Returns a deep copy of `value` that can be changed without affecting the original.
 *
 * @remarks
 * The copy preserves plain-object key order and prototypes, sparse-array holes, shared references,
 * cycles, the link between each URL and its `searchParams` object and the sharing between buffers
 * and their views. Plain objects, arrays, `Map`, `Set`, `Date`, `ArrayBuffer`, `DataView`, typed
 * arrays, `URL`, `URLSearchParams` and Temporal values are supported.
 *
 * Primitives, including bigints, are returned as they are. Objects kept by reference are shared
 * with the original: functions, a `RegExp`, `Error`, `Promise`, `WeakMap`, `WeakSet`, `WeakRef`,
 * `FinalizationRegistry`, `Blob` or `SharedArrayBuffer`, a boxed primitive and an instance of a
 * subclass of one of them. A view over a `SharedArrayBuffer` is copied over that same buffer.
 * Temporal support uses the eight value classes on the current global `Temporal` namespace, without
 * installing a polyfill. Other objects, such as class instances, are copied like plain objects. The
 * copy has the same prototype and own properties, as writable, configurable data properties that
 * keep their enumerability. It has no private fields, so a getter or method that uses one throws on
 * the copy. The entries, time, bytes or text of a `Map`, `Set`, `Date`, buffer, view, URL or
 * `URLSearchParams` are read, and its copy filled, with the built-in methods, so no override on a
 * subclass or on the instance runs, such as a `Map` subclass's `set` or `entries`. A copy of an
 * array, `Map`, `Set`, `Date`, buffer, view, URL, `URLSearchParams` or Temporal value also keeps
 * its source's prototype, so an instance of a subclass stays one, but it holds only the elements,
 * entries, time, bytes or text, without other own properties such as fields that a subclass
 * declares.
 *
 * A copied object that relies on functions can still run code that belongs to the original. A `__proto__` key is copied as an own data property. Built-in values from another
 * iframe or Node.js `vm` context, such as a `Map`, `Date` or `RegExp`, are not recognized and are
 * copied like class instances, so the copy's built-in methods throw. Arrays from another context
 * are copied as arrays.
 *
 * @example
 * ```ts
 * const node = { label: 'a', children: [] as unknown[] }
 * node.children.push(node)
 * const copy = snapshot(node) as typeof node
 * // copy !== node; copy.children[0] === copy
 * ```
 *
 * @param value - The value to copy.
 * @param seen - Copies to use for source objects. `snapshot` uses each entry as given, without
 * checking it, and adds an entry for every object it copies. The result is detached only if every
 * supplied entry is a detached copy of its source. Map a URL and its `searchParams` together, to a
 * copy whose `searchParams` is the mapped entry, or map neither. Mapping only the `searchParams`
 * of a URL in `value` throws `SnapshotURLSearchParamsMemoIncompatible`. Mapping only the URL
 * leaves a copy of its `searchParams` elsewhere in the result unlinked from the mapped URL.
 * @returns A copy of `value`, detached unless `seen` supplies entries that are not, or `value`
 * itself when it is not an object.
 * @throws {@link ReconcileError} with type `SnapshotURLSearchParamsMemoIncompatible` when `seen`
 * maps the `searchParams` of a URL in `value` but not the URL.
 * @throws Errors thrown by getters or proxy traps propagate unchanged.
 */
export function snapshot(
  value: unknown,
  seen: WeakMap<object, object> | undefined = undefined,
): unknown {
  return new SnapshotWalk(seen).root(value)
}

type Begin = (layout: Layout) => void
type Deliver = (
  value: unknown,
  key?: PropertyKey,
  knownKind?: symbol,
  construction?: boolean,
) => unknown

/**
 * One snapshot call's traversal state. Its methods are the walk's steps, so a call allocates
 * this object rather than one closure per step, and its reference memo only when it looks an
 * object up.
 *
 * @remarks
 * The traversal memoizes the private reference before observing children: the first object's in
 * `firstSource` and `firstReference`, and from the first lookup every object's in `references`.
 * Without a caller memo, a completed reference resolves to its target; a pending one stays a
 * node edge. The facets call `begin` and `edge` only while their own `observe` runs and never
 * catch a callback's exception, so one pair of callbacks, created when the first facet runs,
 * serves every node, routed through `currentReference` to the node being observed.
 */
class SnapshotWalk extends Detached {
  declare beginCallback: Begin | undefined
  declare readonly callerMemo: WeakMap<object, object> | undefined
  declare constructed: WeakMap<object, object> | undefined
  declare count: number
  declare currentReference: SnapshotReference | undefined
  declare currentSource: object | undefined
  declare edgeCallback: Deliver | undefined
  /** The first object the walk observes and its reference, copied into `references` when it is
   * made. */
  declare firstReference: SnapshotReference | undefined
  declare firstSource: object | undefined
  /** The prototype recognition read for the object `observe` is on, before it recurses. */
  declare readonly read: PrototypeRead
  /** Every observed object's reference, made at the walk's first lookup. */
  declare references: Map<object, SnapshotReference> | undefined

  constructor(seen: WeakMap<object, object> | undefined) {
    super()
    this.callerMemo = seen
    this.read = { known: false, prototype: null }
    this.references = undefined
    this.firstReference = undefined
    this.firstSource = undefined
    this.constructed = undefined
    this.count = 0
    this.currentReference = undefined
    this.currentSource = undefined
    this.beginCallback = undefined
    this.edgeCallback = undefined
  }

  edgeOf(source: unknown, kind?: symbol): Edge {
    if (!isObject(source)) return source as Primitive
    const seen = this.callerMemo
    if (seen !== undefined) {
      const external = seen.get(source)
      if (external !== undefined) return { node: undefined, value: external }
    }
    const reference = this.memoized(source)
    if (reference === undefined) return this.observe(source, kind)
    const target = seen === undefined ? this.targetOf(reference) : undefined
    return target === undefined ? reference : { node: undefined, value: target }
  }

  // Copies the node, records the construction answer of a copied URLSearchParams, the only facet
  // that has one, then writes the memo.
  begin(layout: Layout): void {
    const reference = this.currentReference!
    const policy = snapshotTypes.policies[layout.kind]
    const target = policy.snapshot(layout)
    reference.layout = layout
    reference.target = target
    if (policy.construction !== noValue)
      (this.constructed ??= new WeakMap()).set(target, policy.construction(layout)!)
    this.remember(this.currentSource!, target)
  }

  // Answers the only edge a facet delivers, a URL's construction edge to its `searchParams`.
  edge(value: unknown, _key?: PropertyKey, knownKind?: symbol): unknown {
    const child = this.edgeOf(value, knownKind)
    if (isNode(child)) {
      const layout = (child as SnapshotReference).layout
      if (layout !== undefined) return snapshotTypes.policies[layout.kind].construction(layout)
      return undefined
    }
    const target = atomValue(child)
    return this.constructed?.get(target as object) ?? target
  }

  // A slot's copied value, as `edgeOf(value)` resolves to it, without allocating the edge: a
  // primitive is itself, an object its caller-memo value or its reference's target.
  slot(value: unknown): unknown {
    if (!isObject(value)) return value
    const seen = this.callerMemo
    if (seen !== undefined) {
      const external = seen.get(value)
      if (external !== undefined) return external
    }
    return this.targetOf(this.memoized(value) ?? this.observe(value))
  }

  // A reference's copy: for a buffer first met through a typed array copied from itself, that
  // copy's buffer, read at the first lookup that needs it (Types.CallTables.pending_run_eq).
  targetOf(reference: SnapshotReference): object | undefined {
    const target = reference.target
    if (target !== undefined || reference.view === undefined) return target
    return (reference.target = typedBufferOf(reference.view))
  }

  // The root's copied value, as `slot` resolves it, without a memo lookup: nothing is memoized yet,
  // so every later lookup follows the first object's observation.
  root(value: unknown): unknown {
    if (!isObject(value)) return value
    const external = this.callerMemo?.get(value)
    if (external !== undefined) return external
    return this.observe(value).target
  }

  // The reference the walk memoized for `source`, if it observed it; the same reference one map for
  // every object returns (Types.CallTables.lazy_run_eq).
  memoized(source: object): SnapshotReference | undefined {
    return (this.references ?? this.memo()).get(source)
  }

  // The memo map, made at the first lookup, which follows the first object's observation, holding
  // that object's reference.
  memo(): Map<object, SnapshotReference> {
    const references = new Map<object, SnapshotReference>()
    references.set(this.firstSource!, this.firstReference!)
    this.references = references
    return references
  }

  // Objects, arrays, Maps and Sets are observed inline, with the same native reads in the same
  // order as their capture `observe`, then the target, the memo write and each slot.
  // fallow-ignore-next-line complexity -- one copy per object; a helper per object costs snapshot time
  observeObject(reference: SnapshotReference, source: object): void {
    const prototype = prototypeOf(source, this.read)
    // The structural scan ends here for atoms too; one more step of the same walk keeps them.
    if (prototype !== Object.prototype && prototype !== null && atomPrototype(prototype)) {
      // Kept by reference.
      reference.target = source
      this.callerMemo?.set(source, source)
      return
    }
    const names = Object.getOwnPropertyNames(source)
    const hidden = hiddenNames(source, names)
    const target = (prototype === Object.prototype ? {} : Object.create(prototype)) as Record<
      PropertyKey,
      unknown
    >
    const standard = standardPrototype(prototype)
    reference.target = target
    this.remember(source, target)
    // On a standard prototype only keys `Object.prototype` holds, such as `__proto__`, and hidden
    // keys need a definition; setOwnProperty decides alike.
    if (standard && hidden === undefined)
      for (let index = 0; index < names.length; index++) {
        const key = names[index]
        const value = this.slot(Reflect.get(source, key))
        if (key in objectPrototype) defineData(target, key, value)
        else target[key] = value
      }
    else
      for (let index = 0; index < names.length; index++) {
        const key = names[index]
        setOwnProperty(
          target,
          key,
          this.slot(Reflect.get(source, key)),
          standard,
          hidden?.has(key) !== true,
        )
      }
    // A symbol is read after its descriptor; one a proxy lists without a descriptor is absent.
    const symbols = Object.getOwnPropertySymbols(source)
    for (let index = 0; index < symbols.length; index++) {
      const key = symbols[index]
      const descriptor = Object.getOwnPropertyDescriptor(source, key)
      if (descriptor === undefined) continue
      setOwnProperty(
        target,
        key,
        this.slot(Reflect.get(source, key)),
        standard,
        descriptor.enumerable === true,
      )
    }
  }

  observeArray(reference: SnapshotReference, source: object): void {
    const array = source as unknown[]
    // Reading the prototype after another read of the array lets the engine fold it.
    const length = array.length
    const target = new Array<unknown>(length)
    const prototype = Object.getPrototypeOf(array) as object | null
    reference.target = target
    this.remember(source, target)
    // The elements are assigned before the copy takes its prototype, so no setter on that
    // prototype runs.
    // The first bound is the length read above; an element read can change it, so each later
    // bound is read again.
    let bound = length
    for (let index = 0; index < bound; index += 1) {
      if (hasElement(array, index)) target[index] = this.slot(array[index])
      bound = array.length
    }
    adoptPrototype(target, prototype, Array.prototype)
  }

  // A Map or Set is read, and its copy filled, with the built-ins, so no override runs.
  observeMap(reference: SnapshotReference, source: object): void {
    const prototype = prototypeOf(source, this.read)
    const target = new Map<unknown, unknown>()
    reference.target = target
    this.remember(source, target)
    forEachBuiltinEntry(source, (child, key) => {
      const copiedKey = this.slot(key)
      builtinMapSet(target, copiedKey, this.slot(child))
    })
    adoptPrototype(target, prototype, Map.prototype)
  }

  observeSet(reference: SnapshotReference, source: object): void {
    const prototype = prototypeOf(source, this.read)
    const target = new Set<unknown>()
    reference.target = target
    this.remember(source, target)
    forEachBuiltinMember(source, (child) => {
      builtinSetAdd(target, this.slot(child))
    })
    adoptPrototype(target, prototype, Set.prototype)
  }

  // Dates, ArrayBuffers, typed arrays and DataViews are observed inline in the same way.
  observeDate(reference: SnapshotReference, value: object): void {
    const target = new Date(timeOf(value))
    adoptPrototype(target, prototypeOf(value, this.read), Date.prototype)
    reference.target = target
    this.callerMemo?.set(value, target)
  }

  observeBuffer(reference: SnapshotReference, value: object): void {
    const target = copyBuffer(value, prototypeOf(value, this.read))
    reference.target = target
    this.callerMemo?.set(value, target)
  }

  // The answer `edge(view.buffer, 'buffer', ARRAY_BUFFER_KIND, true)` gives a view's facet.
  // fallow-ignore-next-line complexity -- repeats each case of the edge's construction answer
  viewBuffer(source: unknown): unknown {
    if (!isObject(source)) return source
    const seen = this.callerMemo
    if (seen !== undefined) {
      const external = seen.get(source)
      if (external !== undefined) return this.constructed?.get(external) ?? external
    }
    const reference = this.memoized(source)
    if (reference === undefined) return this.observe(source, ARRAY_BUFFER_KIND).target
    const target = seen === undefined ? this.targetOf(reference) : undefined
    if (target !== undefined) return this.constructed?.get(target) ?? target
    const layout = reference.layout
    return layout === undefined
      ? undefined
      : snapshotTypes.policies[layout.kind].construction(layout)
  }

  observeView(reference: SnapshotReference, source: object, kind: symbol): void {
    const view = source as ArrayBufferView
    // Recognition's prototype read, taken before the buffer's observation reuses the record, and
    // one read of the element type, which decides every getter below.
    const prototype = prototypeOf(source, this.read)
    const element = viewElement(view)
    const buffer = bufferWith(view, element)
    const target =
      kind === DATA_VIEW_KIND
        ? copyDataView(view, this.viewBuffer(buffer) as ArrayBuffer, prototype, element)
        : this.typedCopy(view, buffer, prototype, element!)
    reference.target = target
    this.callerMemo?.set(source, target)
  }
  // A typed array's copy over its buffer's copy. When the walk meets the buffer first through the
  // array and the caller passed no memo, `copyTypedFirst` copies both, leaving the buffer's copy in
  // its memo entry.
  typedCopy(
    view: ArrayBufferView,
    buffer: ArrayBuffer,
    prototype: object | null,
    element: string,
  ): ArrayBufferView {
    if (this.callerMemo !== undefined)
      return copyTypedArray(view, this.viewBuffer(buffer) as ArrayBuffer, prototype, element)
    const known = this.memoized(buffer)
    if (known !== undefined)
      return copyTypedArray(view, this.targetOf(known) as ArrayBuffer, prototype, element)
    const entry = new SnapshotReference(this.count++)
    this.references!.set(buffer, entry)
    return copyTypedFirst(view, buffer, prototype, element, entry)
  }

  // fallow-ignore-next-line complexity -- one dispatch per node; helper calls here cost snapshot time
  observe(source: object, kind?: symbol): SnapshotReference {
    const reference = new SnapshotReference(this.count++)
    if (reference.node === 0) {
      this.firstReference = reference
      this.firstSource = source
    } else (this.references ?? this.memo()).set(source, reference)
    // The built-in object observer splits atoms itself, with the prototype recognition read. The
    // built-in observers take that read before they recurse into children (Types.Ingress).
    const read = this.read
    read.known = false
    const known = kind ?? recognizeStructure(snapshotTypes, source, read)
    if (known === OBJECT_KIND) {
      this.observeObject(reference, source)
      return reference
    }
    if (known === ARRAY_KIND) {
      this.observeArray(reference, source)
      return reference
    }
    if (known === MAP_KIND) {
      this.observeMap(reference, source)
      return reference
    }
    if (known === SET_KIND) {
      this.observeSet(reference, source)
      return reference
    }
    if (known === DATE_KIND) {
      this.observeDate(reference, source)
      return reference
    }
    if (known === ARRAY_BUFFER_KIND) {
      this.observeBuffer(reference, source)
      return reference
    }
    if (known === TYPED_ARRAY_KIND || known === DATA_VIEW_KIND) {
      this.observeView(reference, source, known)
      return reference
    }
    this.observePolicy(reference, source, known)
    return reference
  }

  // Observes `source` through its kind's facet, which copies it in `begin`; a URL first asks
  // `edge` for its `searchParams`.
  observePolicy(reference: SnapshotReference, source: object, known: symbol): void {
    const policy = snapshotTypes.policies[known]
    const begin = (this.beginCallback ??= (layout) => {
      this.begin(layout)
    })
    const edge = (this.edgeCallback ??= (value, key, knownKind) => this.edge(value, key, knownKind))
    const parent = this.currentReference
    const parentSource = this.currentSource
    this.currentReference = reference
    this.currentSource = source
    policy.observe(source, begin, edge)
    this.currentReference = parent
    this.currentSource = parentSource
  }

  // Records `target` as the caller's copy of `source`.
  remember(source: object, target: object): void {
    this.callerMemo?.set(source, target)
  }
}
