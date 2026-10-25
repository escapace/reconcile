// Realizes graphs in the `Spec` wire form as live objects: plain objects with data and accessor
// slots on their prototype label, arrays with holes and integrity levels, maps, sets and dates.
// The Spec bridge and the invariant tests share it so that one reading of a graph exists.
import assert from 'node:assert/strict'
import {
  ATOMS,
  byKind,
  CLASSES,
  isHole,
  isReference,
  type ByKind,
  type Classes,
  type Extensibility,
  type Graph,
  type GraphNode,
  type NodeOf,
  type Slot,
  type Value,
} from './spec-generator'

/** The prototype objects of the class labels: one object per label. */
export type Prototypes = readonly object[]
/** The slot-free prototypes a graph takes unless a case supplies its own. */
const prototypes: Prototypes = Array.from({ length: CLASSES }, (): object => ({}))
export const prototypeIndex = new Map(prototypes.map((p, index) => [p, index]))
/** The functions the atom labels stand for. */
export const atoms = Array.from({ length: ATOMS }, (_, index) => (): number => index)

/** Getter and setter calls per object and key, recorded by the accessors `materialize` installs. */
export type Counters = Map<object, Map<string, { get: number; set: number }>>
/** Whether an installed setter stores its value, by setter function. */
export const setterStores = new WeakMap<object, boolean>()
export type Resolve = (v: Value) => unknown
type Accessor = Extract<Slot, { get: Value }>

export const primitiveToJs = (v: Exclude<Value, { ref: number }>): unknown =>
  v === null || typeof v !== 'object' ? v : 'undef' in v ? undefined : atoms[v.atom]

export const toJs = (v: Value, objects: readonly object[]): unknown =>
  isReference(v) ? objects[v.ref] : primitiveToJs(v)

const prototypeOf = (prototype: NodeOf<'object'>['proto'], classes: Prototypes): object | null =>
  prototype === 'object' ? Object.prototype : prototype === 'null' ? null : classes[prototype.cls]

const shells: ByKind<[classes: Prototypes], object> = {
  array: () => [],
  date: (node) => new Date(node.ms),
  map: () => new Map(),
  object: (node, classes) => Object.create(prototypeOf(node.proto, classes)) as object,
  set: () => new Set(),
}

const levelers: Record<Extensibility, (a: unknown[]) => unknown> = {
  frozen: Object.freeze,
  nonExtensible: Object.preventExtensions,
  sealed: Object.seal,
  extensible: () => undefined,
}

function defineData(
  o: object,
  key: string,
  slot: Extract<Slot, { v: Value }>,
  resolve: Resolve,
): void {
  Object.defineProperty(o, key, {
    configurable: slot.a[2],
    enumerable: slot.a[1],
    value: resolve(slot.v),
    writable: slot.a[0],
  })
}

/** Fills the shell of a node, resolving each value with `resolve`; an accessor slot goes to
 * `accessor`, which the recipe's created objects do not have. */
const fillers: ByKind<
  [o: object, resolve: Resolve, accessor?: (o: object, key: string, slot: Accessor) => void],
  void
> = {
  array: (node, o, resolve) => {
    const a = o as unknown[]
    a.length = node.entries.length
    node.entries.forEach((entry, index) => {
      if (!isHole(entry)) a[index] = resolve(entry)
    })
    levelers[node.ext](a)
  },
  date: () => undefined,
  map: (node, o, resolve) => {
    for (const [k, v] of node.entries) (o as Map<unknown, unknown>).set(resolve(k), resolve(v))
  },
  object: (node, o, resolve, accessor) => {
    for (const [key, slot] of node.fields) {
      if ('v' in slot) defineData(o, key, slot, resolve)
      else {
        assert.ok(accessor !== undefined, 'a created object has no accessors')
        accessor(o, key, slot)
      }
    }
    if (!node.extensible) Object.preventExtensions(o)
  },
  set: (node, o, resolve) => {
    for (const m of node.members) (o as Set<unknown>).add(resolve(m))
  },
}

/** Builds one object from a node without accessors, as a recipe creates it. */
export function construct(node: GraphNode, resolve: Resolve): object {
  const o = byKind(shells, node, prototypes)
  byKind(fillers, node, o, resolve)
  return o
}

/** Resolves the primitive values of class slots, which reference no node. */
const resolvePrimitive: Resolve = (v) => toJs(v, [])

/** Builds the prototype objects of a case's classes, with their slots; accessors count their
 * calls in `counters`. */
export function materializeClasses(classes: Classes, counters: Counters): object[] {
  return classes.map((slots) => {
    const o = {}
    for (const [key, slot] of slots) {
      if ('v' in slot) defineData(o, key, slot, resolvePrimitive)
      else defineAccessor(o, key, slot, resolvePrimitive, counters)
    }
    return o
  })
}

/** Builds the objects of a graph; `fixed(j)` supplies an existing object for node `j`, `wrap`
 * replaces a new shell before it is filled, and `classes` are the prototypes of the class labels. */
export function materialize(
  graph: Graph,
  counters: Counters,
  fixed: (index: number) => object | undefined = () => undefined,
  wrap: (o: object, index: number) => object = (o) => o,
  classes: Prototypes = prototypes,
): object[] {
  const objects = graph.nodes.map(
    (node, index) => fixed(index) ?? wrap(byKind(shells, node, classes), index),
  )
  const resolve: Resolve = (v) => toJs(v, objects)
  const accessor = (o: object, key: string, slot: Accessor): void =>
    defineAccessor(o, key, slot, resolve, counters)
  graph.nodes.forEach((node, index) => {
    if (fixed(index) === undefined) byKind(fillers, node, objects[index], resolve, accessor)
  })
  return objects
}

function countersOf(counters: Counters, o: object): Map<string, { get: number; set: number }> {
  let byKey = counters.get(o)
  if (byKey === undefined)
    counters.set(o, (byKey = new Map<string, { get: number; set: number }>()))
  return byKey
}

/** Defines an accessor slot whose getter and setter count their calls. */
function defineAccessor(
  o: object,
  key: string,
  slot: Accessor,
  resolve: Resolve,
  counters: Counters,
): void {
  let store = resolve(slot.get)
  const count = { get: 0, set: 0 }
  countersOf(counters, o).set(key, count)
  const stores = slot.set
  const setter = (value: unknown): void => {
    count.set += 1
    if (stores === true) store = value
  }
  setterStores.set(setter, stores === true)
  Object.defineProperty(o, key, {
    configurable: slot.c,
    enumerable: slot.e,
    set: stores === null ? undefined : setter,
    get(): unknown {
      count.get += 1
      return store
    },
  })
}
