// Seeded random graphs and recipes for the `Spec` family, in the wire form `lean/Spec/Graph.lean`
// and `lean/Spec/Produce.lean` read. The generator is deterministic per seed; a differing case is
// reproduced by its seed and options.
import assert from 'node:assert/strict'

export type Attributes = [writable: boolean, enumerable: boolean, configurable: boolean]
export type Extensibility = 'extensible' | 'frozen' | 'nonExtensible' | 'sealed'
export type GraphNode =
  | { entries: Array<[Value, Value]>; kind: 'map' }
  | { entries: Array<Value | { hole: true }>; ext: Extensibility; kind: 'array' }
  | { extensible: boolean; fields: Array<[string, Slot]>; kind: 'object'; proto: Prototype }
  | { kind: 'date'; ms: number }
  | { kind: 'set'; members: Value[] }
export type Kind = GraphNode['kind']
export type NodeOf<K extends Kind> = Extract<GraphNode, { kind: K }>
export type Prototype = 'null' | 'object' | { cls: number }
export type Slot =
  { a: Attributes; v: Value } | { c: boolean; e: boolean; get: Value; set: boolean | null }
export type Value =
  boolean | number | string | { atom: number } | { ref: number } | { undef: true } | null
/** A table of one function per node kind, and the call that dispatches on a node's kind. */
export type ByKind<A extends unknown[], R> = { [K in Kind]: (node: NodeOf<K>, ...rest: A) => R }
export const byKind = <A extends unknown[], R>(
  table: ByKind<A, R>,
  node: GraphNode,
  ...rest: A
): R => (table[node.kind] as (node: GraphNode, ...rest: A) => R)(node, ...rest)

/** The own slots of each class prototype, by class label. */
export interface Case {
  /** The slots the class prototypes hold; empty without the `inherited` option. */
  classes: Classes
  cur: Graph
  next: Graph
  /** Per next node, the current node that is the same object. */
  same: Array<number | null>
}
export type Classes = Array<Array<[string, Slot]>>
export interface Graph {
  nodes: GraphNode[]
  root: Value
}
export interface Options {
  /** Accessor slots in `current`. */
  accessors?: boolean
  /** Non-default attributes and extensibility levels. */
  attributes?: boolean
  /** More accessors, dropping setters and reorders below the root, so that decision passes
   * demote objects more often; the root takes no accessor, so a hazard rarely rejects the call. */
  hazards?: boolean
  /** Data and accessor slots on the class prototypes, and more objects labelled with one. */
  inherited?: boolean
  /** The largest graph. */
  nodes?: number
  /** Key and entry reorders in `next`. */
  reorder?: boolean
  /** Positions of `next` that hold `current` objects. */
  same?: boolean
}

/** A small deterministic PRNG (mulberry32). */
class Rng {
  private state: number
  constructor(seed: number) {
    this.state = seed >>> 0
  }
  chance(p: number): boolean {
    return this.next() < p
  }
  int(bound: number): number {
    return Math.floor(this.next() * bound)
  }
  next(): number {
    this.state = (this.state + 0x6d_2b_79_f5) >>> 0
    let t = this.state
    t = Math.imul(t ^ (t >>> 15), t | 1)
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61)
    return ((t ^ (t >>> 14)) >>> 0) / 4_294_967_296
  }
  pick<T>(items: readonly T[]): T {
    return items[this.int(items.length)]
  }
}

const KEYS = ['a', 'b', 'c', 'd', 'e', 'f']
export const CLASSES = 3
export const ATOMS = 3
/** The reference probability of a slot of a generated node. */
const P_REFERENCE = 0.45

export const isReference = (v: Value): v is { ref: number } =>
  typeof v === 'object' && v !== null && 'ref' in v
export const isHole = (entry: Value | { hole: true }): entry is { hole: true } =>
  typeof entry === 'object' && entry !== null && 'hole' in entry
export const slotValue = (s: Slot): Value => ('v' in s ? s.v : s.get)
const sameValue = (a: Value, b: Value): boolean => JSON.stringify(a) === JSON.stringify(b)
const clone = <T>(value: T): T => JSON.parse(JSON.stringify(value)) as T
/** `list` in a random order. */
const shuffle = <T>(rng: Rng, list: T[]): T[] => list.sort(() => rng.next() - 0.5)
/** Pushes `value` unless an equal one is present. */
function addDistinct(list: Value[], value: Value): void {
  if (!list.some((member) => sameValue(member, value))) list.push(value)
}

const prims: ReadonlyArray<(rng: Rng) => Value> = [
  () => null,
  (rng) => rng.chance(0.5),
  (rng) => rng.int(5),
  (rng) => rng.pick(['x', 'y', 'z']),
  () => ({ undef: true }),
  (rng) => ({ atom: rng.int(ATOMS) }),
  (rng) => rng.int(100) - 50,
]
const prim = (rng: Rng): Value => rng.pick(prims)(rng)

/** A primitive, or with probability `pReference` a reference to one of `references`. */
const value = (rng: Rng, references: readonly number[], pReference: number): Value =>
  references.length > 0 && rng.chance(pReference) ? { ref: rng.pick(references) } : prim(rng)

const attributes = (rng: Rng, allowed: boolean): Attributes =>
  !allowed || rng.chance(0.7)
    ? [true, true, true]
    : [rng.chance(0.6), rng.chance(0.6), rng.chance(0.6)]

function slot(rng: Rng, references: readonly number[], options: Options): Slot {
  const hazards = options.hazards === true
  if (options.accessors === true && rng.chance(hazards ? 0.45 : 0.2))
    return {
      c: rng.chance(0.8),
      e: rng.chance(0.8),
      get: value(rng, references, P_REFERENCE),
      set: hazards ? rng.pick([true, false, false]) : rng.pick([null, true, false]),
    }
  return { a: attributes(rng, options.attributes === true), v: value(rng, references, P_REFERENCE) }
}

function prototype(rng: Rng, options: Options): Prototype {
  const r = rng.next()
  const plain = options.inherited === true ? 0.5 : 0.75
  return r < plain ? 'object' : r < plain + 0.1 ? 'null' : { cls: rng.int(CLASSES) }
}

/** A slot of a class prototype: a primitive data slot or an accessor over a primitive. */
function classSlot(rng: Rng, options: Options): Slot {
  if (rng.chance(0.5))
    return {
      c: rng.chance(0.8),
      e: rng.chance(0.8),
      get: prim(rng),
      set: rng.pick([null, true, false]),
    }
  return { a: attributes(rng, options.attributes === true), v: prim(rng) }
}

/** The slots of each class prototype: up to two per class under the `inherited` option. */
function genClasses(rng: Rng, options: Options): Classes {
  return Array.from({ length: CLASSES }, () =>
    options.inherited === true
      ? shuffle(rng, [...KEYS])
          .slice(0, rng.int(3))
          .map((key): [string, Slot] => [key, classSlot(rng, options)])
      : [],
  )
}

const extensibility = (rng: Rng, allowed: boolean): Extensibility =>
  !allowed || rng.chance(0.8) ? 'extensible' : rng.pick(['nonExtensible', 'sealed', 'frozen'])

/** With half the chance, freezes the slots of an object made non-extensible: every data slot
 * read-only and non-configurable. */
function harden(rng: Rng, fields: Array<[string, Slot]>): void {
  if (!rng.chance(0.5)) return
  for (const f of fields) if ('v' in f[1]) f[1] = { a: [false, f[1].a[1], false], v: f[1].v }
}

function buildObject(rng: Rng, references: readonly number[], options: Options): NodeOf<'object'> {
  const keys = shuffle(rng, [...KEYS]).slice(0, 1 + rng.int(4))
  const fields: Array<[string, Slot]> = keys.map((k) => [k, slot(rng, references, options)])
  const extensible = options.attributes !== true || !rng.chance(0.15)
  if (!extensible) harden(rng, fields)
  return { extensible, fields, kind: 'object', proto: prototype(rng, options) }
}

function buildArray(rng: Rng, references: readonly number[], options: Options): NodeOf<'array'> {
  const entries = Array.from({ length: rng.int(5) }, (): Value | { hole: true } =>
    rng.chance(0.15) ? { hole: true } : value(rng, references, P_REFERENCE),
  )
  return { entries, ext: extensibility(rng, options.attributes === true), kind: 'array' }
}

/** Up to three distinct values, each drawn with `draw`. */
function distinctValues(rng: Rng, draw: () => Value): Value[] {
  const values: Value[] = []
  for (let count = rng.int(4); count > 0; count -= 1) addDistinct(values, draw())
  return values
}

function buildMap(rng: Rng, references: readonly number[]): NodeOf<'map'> {
  const keys = distinctValues(rng, () => value(rng, references, 0.3))
  return { entries: keys.map((k) => [k, value(rng, references, P_REFERENCE)]), kind: 'map' }
}

const builders: {
  [K in Kind]: (rng: Rng, references: readonly number[], options: Options) => GraphNode
} = {
  array: buildArray,
  object: buildObject,
  date: (rng) => ({ kind: 'date', ms: rng.int(1000) * 1000 }),
  map: (rng, references) => buildMap(rng, references),
  set: (rng, references) => ({
    kind: 'set',
    members: distinctValues(rng, () => value(rng, references, 0.4)),
  }),
}

/** Builds a node of a graph whose other nodes are `references`. */
const node = (rng: Rng, references: readonly number[], options: Options, kind?: Kind): GraphNode =>
  builders[
    kind ?? rng.pick(['object', 'object', 'object', 'array', 'array', 'map', 'set', 'date'])
  ](rng, references, options)

/** The values a node holds, keys and values alike. */
const valuesOf: ByKind<[], Value[]> = {
  array: (o) => o.entries.filter((entry): entry is Value => !isHole(entry)),
  date: () => [],
  map: (o) => o.entries.flat(),
  object: (o) => o.fields.map(([, s]) => slotValue(s)),
  set: (o) => o.members,
}

const referencesOf = (o: GraphNode): number[] =>
  byKind(valuesOf, o).flatMap((v) => (isReference(v) ? [v.ref] : []))

/** Every node reachable from the root, in traversal order. */
function reachable(graph: Graph): number[] {
  const out: number[] = []
  const pending = isReference(graph.root) ? [graph.root.ref] : []
  for (const id of pending) {
    if (out.includes(id)) continue
    out.push(id)
    pending.push(...referencesOf(graph.nodes[id]))
  }
  return out
}

/** Hangs node `missing` off a host; a date holds no child. */
const attachers: ByKind<[rng: Rng, missing: number], void> = {
  array: (host, _rng, missing) => host.entries.push({ ref: missing }),
  date: () => undefined,
  map: (host, rng, missing) => {
    const used = new Set(host.entries.map(([k]) => k))
    let key = rng.int(1000)
    while (used.has(key)) key += 1
    host.entries.push([key, { ref: missing }])
  },
  object: (host, rng, missing) => {
    const free = KEYS.find((k) => !host.fields.some(([key]) => key === k))
    const held: Slot = { a: [true, true, true], v: { ref: missing } }
    if (free === undefined) host.fields[rng.int(host.fields.length)][1] = held
    else host.fields.push([free, held])
  },
  set: (host, _rng, missing) => host.members.push({ ref: missing }),
}

/** A `current` graph: a root object or array and up to `options.nodes` nodes, every one reachable,
 * with extra references for sharing and cycles. */
function genCurrent(rng: Rng, options: Options): Graph {
  const size = 1 + rng.int(options.nodes ?? 6)
  const ids = Array.from({ length: size }, (_, index) => index)
  // The root takes a class prototype no more often than without `inherited`, and no accessor
  // under `hazards`, so that a hazard rarely rejects the call.
  const rootOptions: Options = {
    ...options,
    accessors: options.hazards === true ? false : options.accessors,
    inherited: false,
  }
  const nodes: GraphNode[] = ids.map((id) =>
    id === 0
      ? node(rng, ids, rootOptions, rng.pick(['object', 'object', 'array']))
      : node(rng, ids, options),
  )
  // Make every node reachable: hang each unreachable node off a reachable node.
  for (;;) {
    const seen = reachable({ nodes, root: { ref: 0 } })
    const missing = ids.find((id) => !seen.includes(id))
    if (missing === undefined) break
    byKind(attachers, nodes[rng.pick(seen)], rng, missing)
  }
  return { nodes, root: { ref: 0 } }
}

/* ------------------------------------------------------------------------------- next graphs */

const mutateValue = (rng: Rng, v: Value, references: readonly number[]): Value =>
  rng.chance(0.5) ? value(rng, references, 0.4) : v

function mutateArray(n: NodeOf<'array'>, rng: Rng, references: readonly number[]): void {
  n.entries = n.entries.map((entry): Value | { hole: true } =>
    rng.chance(0.3) ? (rng.chance(0.1) ? { hole: true } : value(rng, references, 0.4)) : entry,
  )
  if (rng.chance(0.3)) n.entries = n.entries.slice(0, rng.int(n.entries.length + 1))
  if (rng.chance(0.3)) n.entries.push(value(rng, references, 0.4))
  n.ext = 'extensible'
}

function mutateMap(n: NodeOf<'map'>, rng: Rng, references: readonly number[]): void {
  n.entries = n.entries
    .filter(() => rng.chance(0.8))
    .map(([k, v]) => [k, rng.chance(0.4) ? mutateValue(rng, v, references) : v])
  if (!rng.chance(0.3)) return
  const k = value(rng, references, 0.3)
  if (!n.entries.some(([key]) => sameValue(key, k)))
    n.entries.push([k, value(rng, references, 0.4)])
}

function mutateField(
  rng: Rng,
  f: [string, Slot],
  references: readonly number[],
  options: Options,
): void {
  // With hazards, an accessor's next value changes often, so its setter receives a write.
  if ('get' in f[1] && options.hazards === true && rng.chance(0.7))
    f[1] = { a: [true, true, true], v: value(rng, references, 0.4) }
  else if (rng.chance(0.4))
    f[1] = { a: [true, rng.chance(0.9), true], v: mutateValue(rng, slotValue(f[1]), references) }
  else if ('get' in f[1]) f[1] = { a: [true, true, true], v: f[1].get }
}

function addField(rng: Rng, n: NodeOf<'object'>, references: readonly number[]): void {
  const free = KEYS.filter((k) => !n.fields.some(([key]) => key === k))
  if (free.length === 0) return
  n.fields.push([
    rng.pick(free),
    { a: [true, rng.chance(0.85), true], v: value(rng, references, 0.4) },
  ])
}

function mutateObject(
  n: NodeOf<'object'>,
  rng: Rng,
  references: readonly number[],
  options: Options,
): void {
  for (const f of n.fields) mutateField(rng, f, references, options)
  if (rng.chance(0.3)) n.fields = n.fields.filter(() => rng.chance(0.7))
  if (rng.chance(0.3)) addField(rng, n, references)
}

function mutateSet(n: NodeOf<'set'>, rng: Rng, references: readonly number[]): void {
  n.members = n.members.filter(() => rng.chance(0.8))
  if (rng.chance(0.3)) addDistinct(n.members, value(rng, references, 0.4))
}

const mutators: ByKind<[rng: Rng, references: readonly number[], options: Options], void> = {
  array: mutateArray,
  map: mutateMap,
  object: mutateObject,
  set: mutateSet,
  date: (n, rng) => {
    if (rng.chance(0.5)) n.ms = rng.int(1000) * 1000
  },
}

/** The ordered contents of a node, for reordering. */
const orders: ByKind<[], unknown[]> = {
  array: () => [],
  date: () => [],
  map: (n) => n.entries,
  object: (n) => n.fields,
  set: (n) => n.members,
}

/** Changes the mirror `n` of a current node in place: value edits, key and entry additions,
 * removals and reorders; or a node of another kind. */
function mutateNode(
  rng: Rng,
  n: GraphNode,
  references: readonly number[],
  options: Options,
): GraphNode {
  // With hazards, nodes keep their kind and order more often, so that a kept object's write,
  // not a static refusal, decides the case.
  const hazards = options.hazards === true
  if (rng.chance(hazards ? 0.05 : 0.2))
    return node(rng, references, { ...options, accessors: false, attributes: false })
  byKind(mutators, n, rng, references, options)
  if (options.reorder === true && rng.chance(hazards ? 0.15 : 0.3)) shuffle(rng, byKind(orders, n))
  return n
}

/** Puts a reference at a random position of a host, if it has one. */
const holders: ByKind<[rng: Rng, reference: Value], void> = {
  array: (host, _rng, reference) => host.entries.push(reference),
  date: () => undefined,
  map: (host, rng, reference) => host.entries.push([rng.int(1000) + 1000, reference]),
  object: (host, rng, reference) => {
    if (host.fields.length > 0)
      host.fields[rng.int(host.fields.length)][1] = { a: [true, true, true], v: reference }
  },
  set: (host, _rng, reference) => addDistinct(host.members, reference),
}

/** The positions that hold the current object they mirror, chosen before any node is remapped so
 * that each current object is one next node. */
function pickInPlace(rng: Rng, size: number, options: Options): Set<number> {
  const inPlace = new Set<number>()
  if (options.same !== true) return inPlace
  for (let index = 1; index < size; index += 1) if (rng.chance(0.12)) inPlace.add(index)
  return inPlace
}

/** The next nodes that are current objects: the returned function gives the next node that is
 * current node `c`, added as a remapped copy on first use unless `c` is in place. */
function sameNodes(
  current: Graph,
  nodes: GraphNode[],
  same: Array<number | null>,
  inPlace: Set<number>,
): (c: number) => number {
  const sameOf = new Map<number, number>()
  const of = (c: number): number => {
    const known = sameOf.get(c)
    if (known !== undefined) return known
    const id = inPlace.has(c) ? c : nodes.length
    sameOf.set(c, id)
    if (id === nodes.length) nodes.push({ kind: 'date', ms: 0 })
    same[id] = c
    nodes[id] = remap(current.nodes[c], of)
    return id
  }
  return of
}

/** Positions elsewhere that hold a current object, including cycles back to the current root. */
function addHolders(
  rng: Rng,
  nodes: GraphNode[],
  same: Array<number | null>,
  sameNode: (c: number) => number,
): void {
  const size = same.length
  for (let attempt = rng.int(3); attempt > 0; attempt -= 1) {
    const host = rng.int(size)
    if (same[host] === null) byKind(holders, nodes[host], rng, { ref: sameNode(rng.int(size)) })
  }
}

/** A `next` graph derived from `cur`: the mirror of each node, changed by value edits, key and
 * entry additions, removals and reorders, kind changes, and positions that hold `current`
 * objects. Returns the graph and, per next node, the current node it is. */
function genNext(
  rng: Rng,
  current: Graph,
  options: Options,
): { next: Graph; same: Array<number | null> } {
  const nodes: GraphNode[] = clone(current.nodes)
  const same: Array<number | null> = nodes.map(() => null)
  const size = current.nodes.length
  const references = Array.from({ length: size }, (_, index) => index)
  const inPlace = pickInPlace(rng, size, options)
  const sameNode = sameNodes(current, nodes, same, inPlace)
  for (let index = 0; index < size; index += 1) {
    if (inPlace.has(index)) sameNode(index)
    else nodes[index] = mutateNode(rng, nodes[index], references, options)
  }
  if (options.same === true) addHolders(rng, nodes, same.slice(0, size), sameNode)
  return { next: { nodes, root: { ref: 0 } }, same }
}

const mapSlot = (s: Slot, map: (v: Value) => Value): Slot =>
  'v' in s ? { a: s.a, v: map(s.v) } : { ...s, get: map(s.get) }

const mappers: ByKind<[map: (v: Value) => Value], GraphNode> = {
  array: (o, map) => ({
    ...o,
    entries: o.entries.map((entry) => (isHole(entry) ? entry : map(entry))),
  }),
  date: (o) => ({ ...o }),
  map: (o, map) => ({ ...o, entries: o.entries.map(([k, v]): [Value, Value] => [map(k), map(v)]) }),
  object: (o, map) => ({ ...o, fields: o.fields.map(([k, s]) => [k, mapSlot(s, map)]) }),
  set: (o, map) => ({ ...o, members: o.members.map(map) }),
}

/** A copy of `o` with every reference mapped by `map`. */
export const mapReferences = (o: GraphNode, map: (v: Value) => Value): GraphNode =>
  byKind(mappers, o, map)

/** A copy of a current node whose references point at the next nodes that are those objects. */
const remap = (o: GraphNode, sameNode: (c: number) => number): GraphNode =>
  mapReferences(o, (v) => (isReference(v) ? { ref: sameNode(v.ref) } : v))

export function genCase(seed: number, options: Options): Case {
  const rng = new Rng(seed)
  const classes = genClasses(rng, options)
  const current = genCurrent(rng, options)
  const { next, same } = genNext(rng, current, options)
  assert.equal(same.length, next.nodes.length)
  return { classes, cur: current, next, same }
}

/* ---------------------------------------------------------------- produce recipes */

/** A recipe operation in the wire form `lean/Spec/Produce.lean` reads; `node` is a draft heap id:
 * a current node, or `cur.nodes.length + k` for the `k`th created object. */
export type Op =
  | { index: number; node: number; op: 'setIndex'; value: Value }
  | { key: string; node: number; op: 'deleteKey' }
  | { key: string; node: number; op: 'setKey'; value: Value }
  | { key: Value; node: number; op: 'mapDelete' }
  | { key: Value; node: number; op: 'mapSet'; value: Value }
  | { length: number; node: number; op: 'setLength' }
  | { ms: number; node: number; op: 'setTime' }
  | { node: number; op: 'setAdd'; value: Value }
  | { node: number; op: 'setDelete'; value: Value }
  | { obj: GraphNode; op: 'create' }

/** A step of a path from the root draft to a node's draft. */
export type Step = { index: number } | { key: string } | { mapValue: number } | { member: number }

export interface Recipe {
  cur: Graph
  ops: Op[]
  /** Paths from the root to every current node a recipe can reach as a draft. */
  paths: Map<number, Step[]>
  returns: Value
  returnsCurrent: boolean
}

/** The children a draft reaches, with the step to each: properties, elements, map values and set
 * members; a node reachable only as a map key has no draft. */
const draftChildren: ByKind<[], Array<[Value | { hole: true }, Step]>> = {
  array: (o) => o.entries.map((entry, index) => [entry, { index }]),
  date: () => [],
  map: (o) => o.entries.map(([, v], mapValue) => [v, { mapValue }]),
  object: (o) => o.fields.flatMap(([key, s]) => ('v' in s ? [[s.v, { key }]] : [])),
  set: (o) => o.members.map((m, member) => [m, { member }]),
}

/** Records the path to a child not yet reached, and queues it. */
function reachChild(
  paths: Map<number, Step[]>,
  pending: number[],
  path: Step[],
  [v, step]: [Value | { hole: true }, Step],
): void {
  if (isHole(v) || !isReference(v) || paths.has(v.ref)) return
  paths.set(v.ref, [...path, step])
  pending.push(v.ref)
}

function draftPaths(graph: Graph): Map<number, Step[]> {
  const paths = new Map<number, Step[]>()
  if (!isReference(graph.root)) return paths
  paths.set(graph.root.ref, [])
  const pending = [graph.root.ref]
  for (const id of pending)
    for (const child of byKind(draftChildren, graph.nodes[id]))
      reachChild(paths, pending, paths.get(id)!, child)
  return paths
}

/** The simulated draft heap of a recipe: its random source and the values a recipe may write. */
interface Simulation {
  rng: Rng
  value: (pReference?: number) => Value
}

/** An index to write: a present one, or past the end of an extensible array; none when the
 * array has no element and cannot grow. */
function indexToWrite(rng: Rng, target: NodeOf<'array'>): number | undefined {
  const present = target.entries.flatMap((entry, index) => (isHole(entry) ? [] : [index]))
  if (target.ext === 'extensible' && rng.chance(0.4)) return rng.int(target.entries.length + 2)
  return present.length === 0 ? undefined : rng.pick(present)
}

function setIndexOp(target: NodeOf<'array'>, sim: Simulation, id: number): Op | undefined {
  const index = indexToWrite(sim.rng, target)
  if (index === undefined) return undefined
  const value = sim.value()
  while (target.entries.length <= index) target.entries.push({ hole: true })
  target.entries[index] = value
  return { index, node: id, op: 'setIndex', value }
}

function setLengthOp(target: NodeOf<'array'>, sim: Simulation, id: number): Op | undefined {
  if (target.ext === 'sealed') return undefined
  const length = sim.rng.int(target.entries.length + 2)
  target.entries = target.entries.slice(0, length)
  while (target.entries.length < length) target.entries.push({ hole: true })
  return { length, node: id, op: 'setLength' }
}

/** A write to an array draft, applied to the simulation: an element, or the length. */
function arrayOp(target: NodeOf<'array'>, sim: Simulation, id: number): Op | undefined {
  if (target.ext === 'frozen') return undefined
  return sim.rng.chance(0.5) ? setIndexOp(target, sim, id) : setLengthOp(target, sim, id)
}

function mapSetOp(target: NodeOf<'map'>, sim: Simulation, id: number): Op {
  const { rng } = sim
  const key =
    rng.chance(0.5) && target.entries.length > 0 ? rng.pick(target.entries)[0] : sim.value(0.3)
  const value = sim.value()
  const existing = target.entries.find(([k]) => sameValue(k, key))
  if (existing === undefined) target.entries.push([key, value])
  else existing[1] = value
  return { key, node: id, op: 'mapSet', value }
}

/** A write to a `Map` draft: an entry set or deleted. */
function mapOp(target: NodeOf<'map'>, sim: Simulation, id: number): Op | undefined {
  if (sim.rng.chance(0.6)) return mapSetOp(target, sim, id)
  if (target.entries.length === 0) return undefined
  const [key] = sim.rng.pick(target.entries)
  target.entries = target.entries.filter(([k]) => !sameValue(k, key))
  return { key, node: id, op: 'mapDelete' }
}

/** A writable key of `target` set to a new value. */
function setKeyOp(target: NodeOf<'object'>, sim: Simulation, id: number): Op | undefined {
  const writable = target.fields.filter(([, s]) => 'v' in s && s.a[0])
  if (writable.length === 0) return undefined
  const [key] = sim.rng.pick(writable)
  const value = sim.value()
  target.fields = target.fields.map(([k, s]) =>
    k === key && 'v' in s ? [k, { a: s.a, v: value }] : [k, s],
  )
  return { key, node: id, op: 'setKey', value }
}

/** A key added to an extensible `target`. */
function addKeyOp(target: NodeOf<'object'>, sim: Simulation, id: number): Op | undefined {
  const free = KEYS.filter((k) => !target.fields.some(([key]) => key === k))
  if (!target.extensible || free.length === 0) return undefined
  const key = sim.rng.pick(free)
  const value = sim.value()
  target.fields.push([key, { a: [true, true, true], v: value }])
  return { key, node: id, op: 'setKey', value }
}

/** A configurable key of `target` deleted. */
function deleteKeyOp(target: NodeOf<'object'>, sim: Simulation, id: number): Op | undefined {
  const deletable = target.fields.filter(([, s]) => ('v' in s ? s.a[2] : s.c))
  if (deletable.length === 0) return undefined
  const [key] = sim.rng.pick(deletable)
  target.fields = target.fields.filter(([k]) => k !== key)
  return { key, node: id, op: 'deleteKey' }
}

/** A write to an object draft: a writable key set, a key added, or a configurable key deleted. */
function objectOp(target: NodeOf<'object'>, sim: Simulation, id: number): Op | undefined {
  if (!sim.rng.chance(0.5)) return deleteKeyOp(target, sim, id)
  const sets = sim.rng.chance(0.6) ? setKeyOp(target, sim, id) : undefined
  return sets ?? addKeyOp(target, sim, id)
}

/** A write to a `Set` draft: a member added or deleted. */
function setOp(target: NodeOf<'set'>, sim: Simulation, id: number): Op | undefined {
  if (sim.rng.chance(0.6)) {
    const value = sim.value()
    addDistinct(target.members, value)
    return { node: id, op: 'setAdd', value }
  }
  if (target.members.length === 0) return undefined
  const value = sim.rng.pick(target.members)
  target.members = target.members.filter((m) => !sameValue(m, value))
  return { node: id, op: 'setDelete', value }
}

/** A write a draft of the node accepts, applied to the simulation, or none. */
const draftOps: ByKind<[sim: Simulation, id: number], Op | undefined> = {
  array: arrayOp,
  map: mapOp,
  object: objectOp,
  set: setOp,
  date: (target, sim, id) => {
    const ms = sim.rng.int(1000) * 1000
    target.ms = ms
    return { ms, node: id, op: 'setTime' }
  },
}

/** What the recipe returns: usually the root draft, else a draft or created object, or a primitive. */
function returnsOf(
  rng: Rng,
  current: Graph,
  references: readonly number[],
): Pick<Recipe, 'returns' | 'returnsCurrent'> {
  const r = rng.next()
  const root = isReference(current.root) ? current.root.ref : 0
  const returns: Value =
    r < 0.7 ? { ref: root } : r < 0.9 ? { ref: rng.pick(references) } : prim(rng)
  return { returns, returnsCurrent: r < 0.08 }
}

/** Generates a recipe over `cur`: operations a draft accepts, on nodes reachable as drafts, with
 * values that are primitives, drafts of current nodes or created objects. The draft heap is
 * simulated so that no generated operation is refused. */
function genRecipe(rng: Rng, current: Graph, options: Options): Recipe {
  const paths = draftPaths(current)
  const heap: GraphNode[] = clone(current.nodes)
  const ops: Op[] = []
  const draftIds = [...paths.keys()]
  const created: number[] = []
  const anyReference = (): number[] => [...draftIds, ...created]
  const sim: Simulation = {
    rng,
    value: (pReference = 0.4) => value(rng, anyReference(), pReference),
  }
  for (let count = rng.int(7); count > 0; count -= 1) {
    if (rng.chance(0.15)) {
      const object = node(rng, anyReference(), { ...options, accessors: false, attributes: false })
      ops.push({ obj: object, op: 'create' })
      created.push(heap.push(object) - 1)
      continue
    }
    const id = rng.pick(draftIds)
    const op = byKind(draftOps, heap[id], sim, id)
    if (op !== undefined) ops.push(op)
  }
  return { cur: current, ops, paths, ...returnsOf(rng, current, anyReference()) }
}

export function genProduceCase(seed: number, options: Options): Recipe {
  const rng = new Rng(seed)
  const current = genCurrent(rng, { ...options, accessors: false })
  return genRecipe(rng, current, options)
}
