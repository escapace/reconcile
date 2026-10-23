import { atomValue, isNode, snapshotValue } from './graph/edge'
import { noValue } from './types/shared/empty'
import { isObject } from './object-property'
import { recognize, recognizeStructure } from './adapters/recognition'
import { ATOM_KIND } from './constants'
import { atomPrototype, hiddenNames, isEnumerable, prototypeOf } from './object-property'
import type {
  Edge,
  Layout,
  Primitive,
  PrototypeRead,
  SnapshotWrite,
  SnapshotRegistry,
} from './types'
import { snapshotTypes } from './types/builtins'
import { setOwnProperty, standardPrototype } from './set-own-property'
import { eachOpenedEntry } from './types/shared/collection'
import { adoptPrototype } from './types/shared/prototype'
import { OBJECT_KIND } from './types/object'
import { ARRAY_KIND } from './types/array'
import { MAP_KIND } from './types/map'
import { SET_KIND } from './types/set'
import { DATE_KIND, timeOf } from './types/date'
import { ARRAY_BUFFER_KIND } from './types/array-buffer'
import { TYPED_ARRAY_KIND, copyTypedArray } from './types/typed-array'
import { DATA_VIEW_KIND, copyDataView } from './types/data-view'
import { Detached, defineData, hasElement } from './standard-prototypes'

// Read once: `key in Object.prototype` decides each new object's write.
const objectPrototype = /* @__PURE__ */ (() => Object.prototype)()

/**
 * Owns pending or initialized snapshot state on the canonical traversal reference.
 *
 * @remarks
 * Initialization completes before the target enters the public memo. There is no parallel
 * writer table; SnapshotOwner proves the finite installation/resolution trace correspondence.
 */
class SnapshotReference extends Detached {
  declare layout: Layout | undefined
  declare readonly node: number
  declare target: object | undefined
  declare write: SnapshotWrite | undefined

  constructor(node: number) {
    super()
    this.node = node
    this.layout = undefined
    this.target = undefined
    this.write = undefined
  }

  initialize(layout: Layout, target: object, write: SnapshotWrite): void {
    this.layout = layout
    this.target = target
    this.write = write
  }
}

/**
 * Returns a deep copy of `value` that can be changed without affecting the original.
 *
 * @remarks
 * The copy preserves plain-object key order and prototypes, sparse-array holes, shared references,
 * cycles, the link between each URL and its `searchParams` object and the sharing between buffers
 * and their views. Plain objects, arrays, `Map`, `Set`, `Date`, `ArrayBuffer`, `DataView`, typed
 * arrays, `URL`, `URLSearchParams` and Temporal values are supported, including Vue reactive
 * proxies of objects, arrays, maps and sets.
 *
 * Primitives, including bigints, are returned as they are. Objects kept by reference are shared
 * with the original: functions, a `RegExp`, `Error`, `Promise`, `WeakMap`, `WeakSet`, `WeakRef`,
 * `FinalizationRegistry` or `Blob`, a boxed primitive and an instance of a subclass of one of them.
 * Temporal support uses the eight value classes on the current global `Temporal` namespace, without
 * installing a polyfill. Other objects, such as class instances, are copied like plain objects. The
 * copy has the same prototype and own properties, as writable, configurable data properties that
 * keep their enumerability. It has no private fields, so a getter or method that uses one throws on
 * the copy. Building the copy runs no setter on its prototype. A copy of an array, `Map`, `Set`,
 * `Date`, buffer, view, URL, `URLSearchParams` or Temporal value also keeps its source's prototype,
 * so an instance of a subclass stays one, but it holds only the elements, entries, time, bytes or
 * text, without other own properties such as fields that a subclass declares.
 *
 * A copied object that relies on functions, such as a Vue ref, can still run code that belongs to
 * the original. A `__proto__` key is copied as an own data property. Built-in values from another
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
  return snapshotWith(snapshotTypes, value, seen)
}

export function snapshotWith(
  types: SnapshotRegistry,
  value: unknown,
  seen?: WeakMap<object, object>,
): unknown {
  // Custom facets may retain and reinitialize a writer after returning. Their memo
  // remains independent. Built-ins initialize once and expose no reentrant callback
  // before the former memo write; future facets must preserve that boundary.
  if (seen === undefined && types !== snapshotTypes) seen = new WeakMap()
  return new SnapshotWalk(types, seen).slot(value)
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
 * this object and its reference memo rather than one closure per step.
 *
 * @remarks
 * The traversal memoizes the private reference in `references` before observing children.
 * Without a caller memo, a completed reference resolves to its target; a pending one stays a
 * node edge. Built-in facets call `begin` and `edge` only while their own `observe` runs and
 * never catch a callback's exception, so one pair of callbacks, created when the first facet
 * runs, serves every node, routed through `currentReference` to the node being observed.
 * Custom facets may keep a callback and call it later, so each of their nodes gets a pair that
 * routes to it for the duration of the call.
 */
class SnapshotWalk extends Detached {
  declare beginCallback: Begin | undefined
  declare readonly builtin: boolean
  declare readonly callerMemo: WeakMap<object, object> | undefined
  declare constructed: WeakMap<object, object> | undefined
  declare count: number
  declare currentReference: SnapshotReference | undefined
  declare currentSource: object | undefined
  declare edgeCallback: Deliver | undefined
  /** The prototype recognition read for the object `observe` is on, before it recurses. */
  declare readonly read: PrototypeRead
  declare readonly references: Map<object, SnapshotReference>
  declare readonly types: SnapshotRegistry

  constructor(types: SnapshotRegistry, seen: WeakMap<object, object> | undefined) {
    super()
    this.types = types
    this.callerMemo = seen
    this.builtin = types === snapshotTypes
    this.read = { known: false, prototype: null }
    this.references = new Map()
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
    const reference = this.references.get(source)
    if (reference === undefined) return this.observe(source, kind)
    const target = seen === undefined ? reference.target : undefined
    return target === undefined ? reference : { node: undefined, value: target }
  }

  // Initializes the node's writer, records construction metadata, then writes the memo.
  begin(layout: Layout): void {
    const reference = this.currentReference!
    const policy = this.types.policies[layout.kind]
    policy.snapshot(layout, snapshotValue, reference)
    if (policy.construction !== noValue) {
      const response = policy.construction(layout)
      if (response === reference.target) this.constructed?.delete(reference.target!)
      else if (response !== undefined)
        (this.constructed ??= new WeakMap()).set(reference.target!, response)
    }
    this.callerMemo?.set(this.currentSource!, reference.target!)
  }

  // Delivers one slot of the node and answers a construction edge.
  edge(value: unknown, key?: PropertyKey, knownKind?: symbol, construction?: boolean): unknown {
    const reference = this.currentReference!
    const child = this.edgeOf(value, knownKind)
    reference.write?.(child, key)
    if (construction === true) {
      if (isNode(child)) {
        const layout = (child as SnapshotReference).layout
        if (layout !== undefined) return this.types.policies[layout.kind].construction(layout)
      } else {
        const target = atomValue(child)
        return (isObject(target) ? this.constructed?.get(target) : undefined) ?? target
      }
    }
    return undefined
  }

  // Runs a callback with `reference` as the current node, restoring the previous one.
  routed<A extends unknown[], T>(
    reference: SnapshotReference,
    source: object,
    callback: (...a: A) => T,
  ): (...values: A) => T {
    return (...values: A): T => {
      const parent = this.currentReference
      const parentSource = this.currentSource
      this.currentReference = reference
      this.currentSource = source
      try {
        return callback(...values)
      } finally {
        this.currentReference = parent
        this.currentSource = parentSource
      }
    }
  }

  // A slot's copied value, exactly as `snapshotValue(edgeOf(value))` resolves it, without
  // allocating the edge: a primitive is itself, an object its caller-memo value or its
  // reference's target.
  slot(value: unknown): unknown {
    if (!isObject(value)) return value
    const seen = this.callerMemo
    if (seen !== undefined) {
      const external = seen.get(value)
      if (external !== undefined) return external
    }
    return (this.references.get(value) ?? this.observe(value)).target
  }

  // The built-in object, array, Map and Set facets, observed inline for the exact built-in
  // registry: the same native reads in the same order as their `observe`, then the target their
  // writer would create, the memo write, and each slot as their writer would store it.
  observeObject(reference: SnapshotReference, source: object): void {
    const prototype = prototypeOf(source, this.read)
    // The structural scan ends here for atoms too; one more step of the same walk keeps them.
    if (prototype !== Object.prototype && prototype !== null && atomPrototype(prototype)) {
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
    this.callerMemo?.set(source, target)
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
      for (const key of names)
        setOwnProperty(
          target,
          key,
          this.slot(Reflect.get(source, key)),
          standard,
          hidden?.has(key) !== true,
        )
    for (const key of Object.getOwnPropertySymbols(source))
      setOwnProperty(
        target,
        key,
        this.slot(Reflect.get(source, key)),
        standard,
        isEnumerable(source, key),
      )
  }

  observeArray(reference: SnapshotReference, source: object): void {
    const array = source as unknown[]
    // Reading the prototype after another read of the array lets the engine fold it.
    const length = array.length
    const target = new Array<unknown>(length)
    adoptPrototype(target, Object.getPrototypeOf(array) as object | null, Array.prototype)
    reference.target = target
    this.callerMemo?.set(source, target)
    for (let index = 0; index < array.length; index += 1)
      if (hasElement(array, index)) target[index] = this.slot(array[index])
  }

  observeMap(reference: SnapshotReference, source: object): void {
    const method = (source as { entries?: unknown }).entries
    const entries: unknown = Reflect.apply(method as () => unknown, source, [])
    const target = new Map<unknown, unknown>()
    adoptPrototype(target, prototypeOf(source, this.read), Map.prototype)
    reference.target = target
    this.callerMemo?.set(source, target)
    eachOpenedEntry(entries, method, (key, child) => {
      const copiedKey = this.slot(key)
      target.set(copiedKey, this.slot(child))
      return false
    })
  }

  observeSet(reference: SnapshotReference, source: object): void {
    const values = (source as Set<unknown>).values()
    const target = new Set<unknown>()
    adoptPrototype(target, prototypeOf(source, this.read), Set.prototype)
    reference.target = target
    this.callerMemo?.set(source, target)
    for (const child of values) target.add(this.slot(child))
  }

  // The Date, ArrayBuffer, typed-array and DataView facets, observed inline in the same way.
  observeDate(reference: SnapshotReference, value: object): void {
    const target = new Date(timeOf(value))
    adoptPrototype(target, prototypeOf(value, this.read), Date.prototype)
    reference.target = target
    this.callerMemo?.set(value, target)
  }

  // An ArrayBuffer's construction answer is its copied bytes, which are its target, so its
  // inline observation also clears that target's construction metadata as `begin` would.
  observeBuffer(reference: SnapshotReference, value: object): void {
    const target = (value as ArrayBuffer).slice(0)
    reference.target = target
    this.constructed?.delete(target)
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
    const reference = this.references.get(source)
    if (reference === undefined) return this.observe(source, ARRAY_BUFFER_KIND).target
    const target = seen === undefined ? reference.target : undefined
    if (target !== undefined) return this.constructed?.get(target) ?? target
    const layout = reference.layout
    return layout === undefined ? undefined : this.types.policies[layout.kind].construction(layout)
  }

  observeView(reference: SnapshotReference, source: object, kind: symbol): void {
    const view = source as ArrayBufferView
    const buffer = this.viewBuffer(view.buffer) as ArrayBuffer
    const target =
      kind === DATA_VIEW_KIND ? copyDataView(view, buffer) : copyTypedArray(view, buffer)
    reference.target = target
    this.callerMemo?.set(source, target)
  }

  // fallow-ignore-next-line complexity -- one dispatch per node; helper calls here cost snapshot time
  observe(source: object, kind?: symbol): SnapshotReference {
    const reference = new SnapshotReference(this.count++)
    this.references.set(source, reference)
    // The built-in object observer splits atoms itself, with the prototype recognition read. The
    // built-in observers take that read before they recurse into children (Types.Ingress).
    const read = this.read
    read.known = false
    const known =
      kind ??
      (this.builtin
        ? recognizeStructure(this.types, source, read)
        : recognize(this.types, source, read))
    if (known === ATOM_KIND) {
      // An atom is kept by reference, as a function is.
      reference.target = source
      this.callerMemo?.set(source, source)
      return reference
    }
    if (this.builtin) {
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
    }
    const policy = this.types.policies[known]
    const begin = (this.beginCallback ??= (layout) => {
      this.begin(layout)
    })
    const edge = (this.edgeCallback ??= (value, key, knownKind, construction) =>
      this.edge(value, key, knownKind, construction))
    if (!this.builtin) {
      policy.observe(
        source,
        this.routed(reference, source, begin),
        this.routed(reference, source, edge),
        'snapshot',
      )
      return reference
    }
    const parent = this.currentReference
    const parentSource = this.currentSource
    this.currentReference = reference
    this.currentSource = source
    policy.observe(source, begin, edge, 'snapshot')
    this.currentReference = parent
    this.currentSource = parentSource
    return reference
  }
}
