// Random differential bridge for the `Spec` family: generates graphs, runs the production
// runtime on real objects built from them, recaptures the result as a graph (identities, values,
// descriptors, prototypes, extensibility) and compares it with the Lean reference model's result
// on the same case. Getter counts are compared as a report.
//
// Standalone: pnpm exec tsx scripts/lean-spec-bridge.ts [--op reconcile|produce|snapshot]
//   [--seeds N] [--from S] [--strict] [--dump SEED] [--writes] [--hazards] [--binary] [--features]
//   [--no-same] [--no-reorder] [--no-accessors] [--no-attributes] [--no-inherited] [--nodes N]
import assert from 'node:assert/strict'
import { parseArgs } from 'node:util'
import { isReconcileError, produce, reconcile, snapshot } from '../src/index'
import type { Oracle } from './lean-oracle'
import {
  atoms,
  construct,
  materialize,
  materializeClasses,
  primitiveToJs,
  prototypeIndex,
  setterStores,
  toJs,
  type Counters,
  type Resolve,
} from './spec-realize'
import {
  byKind,
  genCase,
  genProduceCase,
  isReference,
  mapReferences,
  slotValue,
  type ByKind,
  type Case,
  type Extensibility,
  type Graph,
  type GraphNode,
  type NodeOf,
  type Op,
  type Options,
  type Recipe,
  type Slot,
  type Step,
  type Value,
  type ViewConstructor,
} from './spec-generator'

const sortedEntries = (v: Record<string, unknown>): Record<string, unknown> =>
  Object.fromEntries(Object.entries(v).sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0)))

/** JSON text with object keys sorted at every level, so Lean's and the runtime's encodings compare. */
const stable = (value: unknown): string =>
  JSON.stringify(value, (_key, v: unknown) =>
    v !== null && typeof v === 'object' && !Array.isArray(v)
      ? sortedEntries(v as Record<string, unknown>)
      : v,
  )

/** A captured result: origins (current index or null) and contents per node in visit order. */
interface Captured {
  nodes: GraphNode[]
  origins: Array<number | null>
  root: Value
}

function atomOf(value: unknown): Value {
  const atom = atoms.indexOf(value as (typeof atoms)[number])
  assert.ok(atom >= 0, 'unknown function in result')
  return { atom }
}

const isObject = (value: unknown): value is object => typeof value === 'object' && value !== null

/** A number of the model is an integer. */
function checked(value: unknown): Value {
  if (typeof value === 'number') assert.ok(Number.isInteger(value), 'non-integer number in result')
  return value as Value
}

/** The model value of a primitive or function, or `undefined` for an object. */
function visitPrimitive(value: unknown): Value | undefined {
  if (value === undefined) return { undef: true }
  if (typeof value === 'function') return atomOf(value)
  return isObject(value) ? undefined : checked(value)
}

/** Reads a live value back into a graph, numbering objects in depth-first visit order; an origin
 * is the object's index in `known`. */
function recapture(root: unknown, known: readonly object[]): Captured {
  const ids = new Map<object, number>()
  const nodes: GraphNode[] = []
  const origins: Array<number | null> = []
  const visit = (value: unknown): Value => {
    const primitive = visitPrimitive(value)
    if (primitive !== undefined) return primitive
    const o = value as object
    const seen = ids.get(o)
    if (seen !== undefined) return { ref: seen }
    const id = nodes.length
    ids.set(o, id)
    nodes.push({ kind: 'date', ms: 0 })
    const origin = known.indexOf(o)
    origins.push(origin >= 0 ? origin : null)
    nodes[id] = encode(o, visit)
    return { ref: id }
  }
  const rootValue = visit(root)
  return { nodes, origins, root: rootValue }
}

/** The extensibility level of an array by the specification's integrity test (V8's `isFrozen`
 * reports an emptied non-extensible array as frozen although its `length` stays writable). */
function arrayLevel(a: unknown[]): Extensibility {
  if (Object.isExtensible(a)) return 'extensible'
  const descriptors = Reflect.ownKeys(a).map((key) => Object.getOwnPropertyDescriptor(a, key)!)
  if (descriptors.some((d) => d.configurable === true)) return 'nonExtensible'
  return descriptors.some((d) => 'value' in d && d.writable === true) ? 'sealed' : 'frozen'
}

type Visit = (value: unknown) => Value

function encodeArray(o: unknown[], visit: Visit): GraphNode {
  const entries: Array<Value | { hole: true }> = []
  for (let index = 0; index < o.length; index += 1)
    entries.push(index in o ? visit(o[index]) : { hole: true })
  return { entries, ext: arrayLevel(o), kind: 'array' }
}

/** The class labels of the prototypes in use: a reconcile case builds its own. */
let classIndex: ReadonlyMap<object, number> = prototypeIndex

function prototypeLabel(o: object): NodeOf<'object'>['proto'] {
  const prototype = Object.getPrototypeOf(o) as object | null
  if (prototype === null) return 'null'
  if (prototype === Object.prototype) return 'object'
  const cls = classIndex.get(prototype)
  assert.ok(cls !== undefined, 'unknown prototype in result')
  return { cls }
}

const attributesOf = (d: PropertyDescriptor): [boolean, boolean, boolean] => [
  d.writable === true,
  d.enumerable === true,
  d.configurable === true,
]

function encodeAccessor(o: object, d: PropertyDescriptor, visit: Visit): Slot {
  // The descriptor's getter is applied to its object, and its setter serves only as a key.
  // eslint-disable-next-line typescript/unbound-method
  const got: unknown = d.get === undefined ? undefined : Reflect.apply(d.get, o, [])
  // eslint-disable-next-line typescript/unbound-method
  const set = d.set === undefined ? null : (setterStores.get(d.set) ?? true)
  return { c: d.configurable === true, e: d.enumerable === true, get: visit(got), set }
}

function encodeField(o: object, key: string, visit: Visit): Slot {
  const d = Object.getOwnPropertyDescriptor(o, key)!
  return 'value' in d ? { a: attributesOf(d), v: visit(d.value) } : encodeAccessor(o, d, visit)
}

const isString = (key: PropertyKey): key is string => typeof key === 'string'

const encodeObject = (o: object, visit: Visit): GraphNode => ({
  extensible: Object.isExtensible(o),
  fields: Reflect.ownKeys(o)
    .filter(isString)
    .map((key) => [key, encodeField(o, key, visit)]),
  kind: 'object',
  proto: prototypeLabel(o),
})

const viewConstructors = new Map<object, ViewConstructor>([
  [DataView.prototype, 'DataView'],
  [Int16Array.prototype, 'Int16Array'],
  [Uint8Array.prototype, 'Uint8Array'],
])

function encodeView(o: ArrayBufferView, visit: Visit): GraphNode {
  const ctor = viewConstructors.get(Object.getPrototypeOf(o) as object)
  assert.ok(ctor !== undefined, 'unknown view constructor in result')
  return { buffer: visit(o.buffer), ctor, kind: 'view', length: o.byteLength, offset: o.byteOffset }
}

/** Encoders by the test that recognizes their kind; a plain object is the last. */
const encoders: ReadonlyArray<
  [test: (o: object) => boolean, encode: (o: never, visit: Visit) => GraphNode]
> = [
  [Array.isArray, encodeArray],
  [
    (o) => o instanceof Map,
    (o: Map<unknown, unknown>, visit) => ({
      entries: [...o].map(([k, v]) => [visit(k), visit(v)]),
      kind: 'map',
    }),
  ],
  [
    (o) => o instanceof Set,
    (o: Set<unknown>, visit) => ({ kind: 'set', members: [...o].map(visit) }),
  ],
  [(o) => o instanceof Date, (o: Date) => ({ kind: 'date', ms: o.getTime() })],
  [
    (o) => o instanceof ArrayBuffer,
    (o: ArrayBuffer) => ({
      bytes: [...new Uint8Array(o)],
      kind: 'buffer',
      // eslint-disable-next-line baseline-js/use-baseline -- the bridge runs on Node 24, which has resizable buffers
      max: o.resizable ? o.maxByteLength : null,
    }),
  ],
  [(o) => ArrayBuffer.isView(o), encodeView],
  [() => true, encodeObject],
]

const encode = (o: object, visit: Visit): GraphNode =>
  encoders.find(([test]) => test(o))![1](o as never, visit)

/** The Lean reference's outcome. For `produce`, an origin is a current index, `-k - 1` for the
 * `k`th object the recipe created, or null for a new object. */
interface Outcome {
  /** Lean encodes a triple as nested pairs; `reconcile` only. */
  nodes: GraphNode[]
  ok: boolean
  origins: Array<number | null>
  gets?: Array<[number, [string, number]]>
  /** 0 when the call is rejected before any write; `reconcile` only. */
  root: Value
  passes?: number
  /** The writes of every decision pass, as `[current index, [key, 'set' | 'delete']]`. */
  allWrites?: Array<[number, [string, string]]>
}

/** Renumbers a graph by depth-first visit order from the root, dropping unreachable nodes. */
function canonicalize(outcome: Outcome): Captured {
  const ids = new Map<number, number>()
  const nodes: GraphNode[] = []
  const origins: Array<number | null> = []
  const visit = (v: Value): Value => {
    if (!isReference(v)) return v
    const seen = ids.get(v.ref)
    if (seen !== undefined) return { ref: seen }
    const id = nodes.length
    ids.set(v.ref, id)
    nodes.push({ kind: 'date', ms: 0 })
    origins.push(outcome.origins[v.ref] ?? null)
    nodes[id] = mapReferences(outcome.nodes[v.ref], visit)
    return { ref: id }
  }
  const root = visit(outcome.root)
  return { nodes, origins, root }
}

interface Report {
  detail: string
  kind:
    | 'attributes'
    | 'current-changed'
    | 'error'
    | 'getters'
    | 'prototype'
    | 'rejection'
    | 'result'
    | 'retention'
    | 'writes'
    | 'wrote-before-rejecting'
  seed: number
}

/** The values a node shows, without attributes, prototype or extensibility. */
const shapes: ByKind<[], unknown> = {
  array: (node) => ({ entries: node.entries, kind: node.kind }),
  buffer: (node) => node,
  date: (node) => node,
  map: (node) => node,
  object: (node) => ({
    fields: node.fields.map(([k, slot]) => [k, slotValue(slot)]),
    kind: node.kind,
  }),
  set: (node) => node,
  view: (node) => node,
}

/** The captured graph's values only: no origins, attributes, prototypes or extensibility. Two
 * results of equal shape that keep different objects differ only in retention. */
const shapeOnly = (captured: Captured): string =>
  stable({ nodes: captured.nodes.map((node) => byKind(shapes, node)), root: captured.root })

const slotWithoutAttributes = (slot: Slot): unknown =>
  'v' in slot ? { v: slot.v } : { get: slot.get, set: slot.set }

/** The captured graph without property attributes, to tell an attribute-only difference apart. */
const withoutAttributes = (captured: Captured): string =>
  stable({
    ...captured,
    nodes: captured.nodes.map((node) =>
      node.kind === 'object'
        ? { ...node, fields: node.fields.map(([k, slot]) => [k, slotWithoutAttributes(slot)]) }
        : node,
    ),
  })

const differenceKind = (actual: Captured, want: Captured): Report['kind'] =>
  withoutAttributes(actual) === withoutAttributes(want)
    ? 'attributes'
    : shapeOnly(actual) === shapeOnly(want)
      ? 'retention'
      : 'result'

/** Reports how the runtime's result differs from the reference's, if it does. */
function compareCaptured(
  seed: number,
  actual: Captured,
  expected: Outcome,
  reports: Report[],
): void {
  const want = canonicalize(expected)
  const actualText = stable(actual)
  const wantText = stable(want)
  if (actualText === wantText) return
  reports.push({
    detail: `runtime ${actualText}\nreference ${wantText}`,
    kind: differenceKind(actual, want),
    seed,
  })
}

const errorReport = (seed: number, error: unknown): Report => ({
  detail: error instanceof Error ? `${error.name}: ${error.message}` : String(error),
  kind: 'error',
  seed,
})

/** Runs `operation`; a rejected publication is a status, any other error is returned. */
interface Attempt {
  rejected: boolean
  error?: unknown
  result?: unknown
}

function attempt(operation: () => unknown): Attempt {
  try {
    return { rejected: false, result: operation() }
  } catch (error) {
    const rejected = isReconcileError(error) && error.cause.type === 'PublicationRejected'
    return rejected ? { rejected } : { error, rejected }
  }
}

/** The getter counts the runtime made so far, labelled `<current index>.<key>`, leaving out the
 * objects `next` holds, whose getters reading `next` runs; then resets the counts. */
function getterCounts(
  counters: Counters,
  current: readonly object[],
  held: ReadonlySet<object>,
): Map<string, number> {
  const counts = new Map<string, number>()
  for (const [o, byKey] of counters)
    for (const [k, count] of byKey) {
      if (!held.has(o)) counts.set(`${current.indexOf(o)}.${k}`, count.get)
      count.get = 0
    }
  return counts
}

/** The getter counts the reference expects, labelled like `getterCounts`. */
const wantedGets = (expected: Outcome, current: readonly object[], held: ReadonlySet<object>) =>
  new Map(
    (expected.gets ?? [])
      .filter(([index]) => !held.has(current[index]))
      .map(([index, [k, n]]) => [`${index}.${k}`, n]),
  )

/** Getter counts for accessor slots of current objects that `next` does not hold, which must
 * agree both ways. */
function reportGetters(
  seed: number,
  actual: ReadonlyMap<string, number>,
  wanted: ReadonlyMap<string, number>,
  reports: Report[],
): void {
  for (const label of new Set([...actual.keys(), ...wanted.keys()])) {
    const n = countOf(actual, label)
    const w = countOf(wanted, label)
    if (n !== w)
      reports.push({ detail: `${label}: runtime ${n} reference ${w}`, kind: 'getters', seed })
  }
}

const countOf = (counts: ReadonlyMap<string, number>, label: string): number =>
  counts.get(label) ?? 0

/** Reports a runtime rejection against the reference: whether the reference succeeds, and whether
 * `current` changed before a rejection the reference decides before any write. */
function reportRejection(seed: number, expected: Outcome, changed: boolean): Report[] {
  const reports: Report[] = []
  if (expected.ok)
    reports.push({ detail: 'runtime rejected; reference succeeds', kind: 'rejection', seed })
  if (changed && expected.passes === 0)
    reports.push({
      detail: 'current changed before a rejection the reference decides before any write',
      kind: 'wrote-before-rejecting',
      seed,
    })
  return reports
}

/** The keys the runtime wrote to each proxied current object, as `key:kind`. */
type Writes = Map<object, Set<string>>

/** Whether `compareReconcile` wraps current objects and arrays in proxies that record writes. */
let writesMode = false

/** A forwarding proxy of `target` that records, while `armed`, the keys set, defined or deleted
 * through it. */
function recordingProxy(target: object, writes: Writes, armed: { on: boolean }): object {
  const record = (key: PropertyKey, kind: string): void => {
    if (!armed.on || typeof key !== 'string') return
    let set = writes.get(proxy)
    if (set === undefined) writes.set(proxy, (set = new Set()))
    set.add(`${key}:${kind}`)
  }
  const proxy: object = new Proxy(target, {
    defineProperty(t, key, descriptor): boolean {
      record(key, 'set')
      return Reflect.defineProperty(t, key, descriptor)
    },
    deleteProperty(t, key): boolean {
      record(key, 'delete')
      return Reflect.deleteProperty(t, key)
    },
    set(t, key, value, receiver): boolean {
      record(key, 'set')
      return Reflect.set(t, key, value, receiver === proxy ? t : receiver)
    },
  })
  return proxy
}

/** Whether a node is an object or array, whose writes the recording proxies see. */
const recorded = (node: GraphNode): boolean => node.kind === 'object' || node.kind === 'array'

/** The keys the reference's passes write on node `index`, as `key:kind`, sorted. */
const wantedWrites = (expected: Outcome, index: number): string =>
  [
    ...new Set(
      (expected.allWrites ?? [])
        .filter(([node]) => node === index)
        .map(([, [k, w]]) => `${k}:${w}`),
    ),
  ]
    .sort()
    .join(' ')

/** The keys the runtime wrote on `object` in any pass, as `key:kind`, sorted. */
const actualWrites = (writes: Writes, object: object): string =>
  [...(writes.get(object) ?? [])].sort().join(' ')

function reportWriteMismatch(
  seed: number,
  index: number,
  actual: string,
  wanted: string,
  reports: Report[],
): void {
  if (actual !== wanted)
    reports.push({
      detail: `${index}: runtime [${actual}] reference [${wanted}]`,
      kind: 'writes',
      seed,
    })
}

/** Reports, for each current object or array, the keys the runtime wrote in any pass against
 * the keys the reference's passes write. */
function reportWrites(
  seed: number,
  c: Case,
  current: readonly object[],
  writes: Writes,
  expected: Outcome,
  reports: Report[],
): void {
  if (!writesMode) return
  for (let index = 0; index < c.cur.nodes.length; index += 1) {
    if (!recorded(c.cur.nodes[index])) continue
    const actual = actualWrites(writes, current[index])
    reportWriteMismatch(seed, index, actual, wantedWrites(expected, index), reports)
  }
}

/** Runs one case through `reconcile` and compares with the reference outcome. */
function compareReconcile(seed: number, c: Case, expected: Outcome): Report[] {
  const counters: Counters = new Map()
  const writes: Writes = new Map()
  const armed = { on: false }
  const wrap = (o: object, index: number): object =>
    writesMode && recorded(c.cur.nodes[index]) ? recordingProxy(o, writes, armed) : o
  const prototypeCounters: Counters = new Map()
  const classes = materializeClasses(c.classes, prototypeCounters)
  classIndex = new Map(classes.map((p, index) => [p, index]))
  const current = materialize(c.cur, counters, undefined, wrap, classes)
  const next = materialize(
    c.next,
    new Map(),
    (index) => (c.same[index] === null ? undefined : current[c.same[index]]),
    undefined,
    classes,
  )
  const held = new Set(c.same.flatMap((index) => (index === null ? [] : [current[index]])))
  const before = stable(recapture(current[0], current))
  getterCounts(counters, current, held)
  armed.on = true
  const run = attempt(() => reconcile(toJs(c.cur.root, current), toJs(c.next.root, next)))
  armed.on = false
  const gets = getterCounts(counters, current, held)
  const reports = reconcileReports(seed, c, expected, run, current, held, before, gets, writes)
  classIndex = prototypeIndex
  return [...reports, ...prototypeReports(seed, prototypeCounters, classes)]
}

/** The reports of a run's outcome against the reference's. */
function reconcileReports(
  seed: number,
  c: Case,
  expected: Outcome,
  run: Attempt,
  current: readonly object[],
  held: ReadonlySet<object>,
  before: string,
  gets: ReadonlyMap<string, number>,
  writes: Writes,
): Report[] {
  if ('error' in run) return [errorReport(seed, run.error)]
  if (run.rejected)
    return reportRejection(seed, expected, stable(recapture(current[0], current)) !== before)
  if (!expected.ok)
    return [{ detail: 'reference rejects; runtime succeeded', kind: 'rejection', seed }]
  const reports: Report[] = []
  compareCaptured(seed, recapture(run.result, current), expected, reports)
  reportGetters(seed, gets, wantedGets(expected, current, held), reports)
  reportWrites(seed, c, current, writes, expected, reports)
  return reports
}

const ran = (count: { get: number; set: number }): boolean => count.get > 0 || count.set > 0

/** `reconcile` reads own properties only and never writes through an inherited accessor, so no
 * getter or setter of a class prototype runs during the call. */
function prototypeReports(seed: number, counters: Counters, classes: readonly object[]): Report[] {
  const reports: Report[] = []
  for (const [o, byKey] of counters)
    for (const [key, count] of byKey)
      if (ran(count))
        reports.push({
          detail: `class ${classes.indexOf(o)} key ${key}: ${count.get} gets, ${count.set} sets`,
          kind: 'prototype',
          seed,
        })
  return reports
}

/** Applies one recipe operation to a draft. */
const appliers: {
  [K in Op['op']]: (op: Extract<Op, { op: K }>, target: unknown, resolve: Resolve) => void
} = {
  create: () => undefined,
  deleteKey: (op, target) => {
    delete (target as Record<string, unknown>)[op.key]
  },
  mapDelete: (op, target, resolve) => (target as Map<unknown, unknown>).delete(resolve(op.key)),
  mapSet: (op, target, resolve) =>
    (target as Map<unknown, unknown>).set(resolve(op.key), resolve(op.value)),
  setAdd: (op, target, resolve) => (target as Set<unknown>).add(resolve(op.value)),
  setByte: (op, target) => {
    new Uint8Array(target as ArrayBuffer)[op.index] = op.byte
  },
  setDelete: (op, target, resolve) => (target as Set<unknown>).delete(resolve(op.value)),
  setIndex: (op, target, resolve) => {
    ;(target as unknown[])[op.index] = resolve(op.value)
  },
  setKey: (op, target, resolve) => {
    ;(target as Record<string, unknown>)[op.key] = resolve(op.value)
  },
  setLength: (op, target) => {
    ;(target as unknown[]).length = op.length
  },
  setTime: (op, target) => (target as Date).setTime(op.ms),
}

const applyOp = (op: Op, target: unknown, resolve: Resolve): void =>
  (appliers[op.op] as (op: Op, target: unknown, resolve: Resolve) => void)(op, target, resolve)

/** The child of a draft at one step of a path. */
function stepInto(o: unknown, step: Step): unknown {
  if ('key' in step) return (o as Record<string, unknown>)[step.key]
  if ('index' in step) return (o as unknown[])[step.index]
  if ('mapValue' in step) return [...(o as Map<unknown, unknown>).values()][step.mapValue]
  return [...(o as Set<unknown>)][step.member]
}

/** Every draft the recipe can reach, by node, read before the first write while the paths hold. */
function reachDrafts(draft: unknown, paths: Recipe['paths']): Map<number, unknown> {
  const drafts = new Map<number, unknown>()
  for (const [id, path] of paths) drafts.set(id, path.reduce(stepInto, draft))
  return drafts
}

/** Runs the recipe through `produce` on real objects; `created` receives the objects it makes. */
function runRecipe(recipe: Recipe, current: readonly object[], created: object[]): unknown {
  const n = current.length
  const root = toJs(recipe.cur.root, current)
  return produce(root, (draft: unknown) => {
    const drafts = reachDrafts(draft, recipe.paths)
    // A node reachable only as a `Map` key has no draft: the recipe holds the key itself.
    const resolve: Resolve = (v) =>
      !isReference(v)
        ? primitiveToJs(v)
        : v.ref < n
          ? (drafts.get(v.ref) ?? current[v.ref])
          : created[v.ref - n]
    for (const op of recipe.ops) {
      if (op.op === 'create') created.push(construct(op.obj, resolve))
      else applyOp(op, drafts.get(op.node), resolve)
    }
    return recipe.returnsCurrent ? root : resolve(recipe.returns)
  })
}

/** Origins of a result as the reference encodes them: `-k - 1` for the `k`th created object. */
const encodeOrigins = (captured: Captured, n: number): Captured => ({
  ...captured,
  origins: captured.origins.map((o) => (o === null ? null : o < n ? o : -(o - n) - 1)),
})

/** Runs `operation` on the objects of `graph`, checks that `current` is unchanged, and compares
 * the result with the reference outcome; `created` lists the objects the operation made. */
function compareCopy(
  seed: number,
  graph: Graph,
  expected: Outcome,
  operation: (current: object[], created: object[]) => unknown,
): Report[] {
  const current = materialize(graph, new Map())
  const before = stable(recapture(current[0], current))
  const created: object[] = []
  const run = attempt(() => operation(current, created))
  if ('error' in run) return [errorReport(seed, run.error)]
  if (!expected.ok)
    return [
      { detail: 'reference refuses an operation; runtime succeeded', kind: 'rejection', seed },
    ]
  const reports: Report[] = []
  if (stable(recapture(current[0], current)) !== before)
    reports.push({ detail: 'current changed', kind: 'current-changed', seed })
  compareCaptured(
    seed,
    encodeOrigins(recapture(run.result, [...current, ...created]), current.length),
    expected,
    reports,
  )
  return reports
}

/** One operation the bridge checks: how a seed becomes a case, the oracle request, and the
 * comparison. */
interface Check<T> {
  compare: (seed: number, c: T, expected: Outcome) => Report[]
  generate: (seed: number, options: Options) => T
  request: (c: T) => object
  show: (c: T) => string
}

const reconcileCheck: Check<Case> = {
  compare: compareReconcile,
  generate: genCase,
  request: (c) => ({
    classes: c.classes,
    cur: c.cur,
    next: c.next,
    op: 'reconcile',
    same: c.same,
  }),
  show: (c) =>
    `cur  ${stable(c.cur)}\nnext ${stable(c.next)}\nsame ${JSON.stringify(c.same)}\nclasses ${JSON.stringify(c.classes)}`,
}

const produceCheck: Check<Recipe> = {
  generate: genProduceCase,
  compare: (seed, r, expected) =>
    compareCopy(seed, r.cur, expected, (current, created) => runRecipe(r, current, created)),
  request: (r) => ({
    cur: r.cur,
    op: 'produce',
    ops: r.ops,
    returns: r.returns,
    returnsCurrent: r.returnsCurrent,
  }),
  show: (r) =>
    `cur ${stable(r.cur)}\nops ${JSON.stringify(r.ops)}\nreturns ${JSON.stringify(r.returns)} returnsCurrent ${r.returnsCurrent}`,
}

const snapshotCheck: Check<Graph> = {
  compare: (seed, graph, expected) =>
    compareCopy(seed, graph, expected, (current) => snapshot(toJs(graph.root, current))),
  generate: (seed, options) => genCase(seed, options).cur,
  request: (graph) => ({ cur: graph, op: 'snapshot' }),
  show: (graph) => `cur ${stable(graph)}`,
}

const checks = { produce: produceCheck, reconcile: reconcileCheck, snapshot: snapshotCheck }

/** Asks the oracle for the outcomes of `requests`, one per request. */
async function ask(oracle: Oracle, requests: readonly object[]): Promise<Outcome[]> {
  const input = JSON.stringify(requests)
  const output = (await oracle('Spec', [], { input, maxBuffer: 64 * 1024 * 1024 })).trim()
  const outcomes = JSON.parse(output) as Outcome[]
  assert.equal(outcomes.length, requests.length)
  return outcomes
}

/** Generates cases from `seeds`, asks the oracle once for all of them and compares. */
async function checkSpec<T>(
  check: Check<T>,
  oracle: Oracle,
  seeds: readonly number[],
  options: Options,
): Promise<{ cases: number; reports: Report[] }> {
  const cases = seeds.map((seed) => check.generate(seed, options))
  const outcomes = await ask(oracle, cases.map(check.request))
  const reports = cases.flatMap((c, index) => check.compare(seeds[index], c, outcomes[index]))
  return { cases: cases.length, reports }
}

/** The seeds `1` to `count`. */
const seeds = (count: number): number[] => Array.from({ length: count }, (_, index) => 1 + index)

function summary(reports: readonly Report[]): string {
  const counts = new Map<string, number>()
  for (const r of reports) counts.set(r.kind, (counts.get(r.kind) ?? 0) + 1)
  const text = [...counts].map(([kind, count]) => `${kind} ${count}`).join(', ')
  return text === '' ? 'agree' : text
}

/** Whether some node of `graph` is on a cycle reachable from the root. */
function hasCycle(graph: Graph): boolean {
  const state = new Map<number, 'done' | 'open'>()
  const visit = (id: number): boolean => {
    const seen = state.get(id)
    if (seen !== undefined) return seen === 'open'
    state.set(id, 'open')
    const node = graph.nodes[id]
    const children = JSON.stringify(node).matchAll(/"ref":(\d+)/g)
    for (const match of children) if (visit(Number(match[1]))) return true
    state.set(id, 'done')
    return false
  }
  return isReference(graph.root) && visit(graph.root.ref)
}

/** How many slots of `graph` reference each node. */
function referrers(graph: Graph): Map<number, number> {
  const counts = new Map<number, number>()
  for (const node of graph.nodes)
    for (const match of JSON.stringify(node).matchAll(/"ref":(\d+)/g)) {
      const id = Number(match[1])
      counts.set(id, (counts.get(id) ?? 0) + 1)
    }
  return counts
}

const orderOf = (node: GraphNode): string =>
  node.kind === 'object'
    ? node.fields.map(([k]) => k).join()
    : node.kind === 'map'
      ? node.entries.map(([k]) => JSON.stringify(k)).join()
      : node.kind === 'set'
        ? node.members.map((m) => JSON.stringify(m)).join()
        : ''

/** Whether two key lists hold the same keys in different orders. */
const permuted = (a: string, b: string): boolean =>
  a !== b && a.split(',').sort().join() === b.split(',').sort().join()

/** Whether the next mirror of current node `index` lists the same keys in another order. */
const reorderedAt = (c: Case, index: number): boolean =>
  c.cur.nodes[index].kind === c.next.nodes[index].kind &&
  c.same[index] === null &&
  permuted(orderOf(c.cur.nodes[index]), orderOf(c.next.nodes[index]))

/** Whether the next mirror of some current node lists the same keys in another order. */
const reordered = (c: Case): boolean => c.cur.nodes.some((_, index) => reorderedAt(c, index))

type Feature = [name: string, present: boolean]
const present = (features: readonly Feature[]): string[] =>
  features.filter(([, p]) => p).map(([name]) => name)

/** The features of a case that its wire text shows. */
const textFeatures = (c: Case): Feature[] => {
  const text = JSON.stringify(c.cur)
  return [
    ['accessor', text.includes('"get":')],
    ['droppingSetter', text.includes('"set":false')],
    [
      'readOnly',
      text.includes('"a":[false') || /"a":\[(?:false|true),(?:false|true),false\]/.test(text),
    ],
    [
      'nonExtensible',
      text.includes('"extensible":false') || /"ext":"(?:frozen|nonExtensible|sealed)"/.test(text),
    ],
    ['hole', text.includes('"hole":true') || JSON.stringify(c.next).includes('"hole":true')],
    ['classPrototype', text.includes('"cls":')],
    ['nullPrototype', text.includes('"proto":"null"')],
  ]
}

/** The features of a case's graphs. */
const graphFeatures = (c: Case): Feature[] => [
  ['cycle', hasCycle(c.cur)],
  ['shared', [...referrers(c.cur).values()].some((n) => n > 1)],
  ['pinned', c.same.some((s) => s !== null)],
  [
    'mapObjectKey',
    c.cur.nodes.some((n) => n.kind === 'map' && n.entries.some(([k]) => isReference(k))),
  ],
  ['date', c.cur.nodes.some((n) => n.kind === 'date')],
  ['rootArray', c.cur.nodes[0].kind === 'array'],
  ['kindChange', c.cur.nodes.some((n, index) => c.next.nodes[index].kind !== n.kind)],
  ['reorder', reordered(c)],
  ['inherited', c.classes.some((slots) => slots.length > 0)],
]

/** The features of a reference outcome. */
const outcomeFeatures = (outcome: Outcome): Feature[] => [
  ['rejected', !outcome.ok],
  ['fresh', outcome.origins.some((o) => o === null)],
  ['getterRan', (outcome.gets ?? []).some(([, [, count]]) => count > 0)],
  ['multiPass', (outcome.passes ?? 1) > 1],
  ['threePasses', (outcome.passes ?? 1) > 2],
]

/** Whether the reference keeps a current object at some next node of `kind`. */
const keepsKind = (c: Case, outcome: Outcome, kind: GraphNode['kind']): boolean =>
  outcome.origins.some((o, index) => o !== null && c.next.nodes[index]?.kind === kind)

/** The buffer and view features of a case and its reference outcome. */
const binaryFeatures = (c: Case, outcome: Outcome): Feature[] => [
  ['buffer', c.cur.nodes.some((n) => n.kind === 'buffer')],
  ['resizable', c.cur.nodes.some((n) => n.kind === 'buffer' && n.max !== null)],
  ['view', c.cur.nodes.some((n) => n.kind === 'view')],
  ['keptBuffer', keepsKind(c, outcome, 'buffer')],
  ['keptView', keepsKind(c, outcome, 'view')],
]

/** The features of a reconcile case and its reference outcome, for the coverage report. */
const caseFeatures = (c: Case, outcome: Outcome): string[] =>
  present([
    ...textFeatures(c),
    ...graphFeatures(c),
    ...outcomeFeatures(outcome),
    ...binaryFeatures(c, outcome),
  ])

/** Prints how often each feature occurs among the reconcile cases of `seedList`. */
async function features(
  oracle: Oracle,
  seedList: readonly number[],
  options: Options,
): Promise<void> {
  const cases = seedList.map((seed) => genCase(seed, options))
  const outcomes = await ask(oracle, cases.map(reconcileCheck.request))
  const counts = new Map<string, number>()
  cases.forEach((c, index) => {
    for (const f of caseFeatures(c, outcomes[index])) counts.set(f, (counts.get(f) ?? 0) + 1)
  })
  console.log(`features over ${cases.length} reconcile cases`)
  for (const [name, count] of [...counts].sort((a, b) => b[1] - a[1]))
    console.log(
      `${name.padEnd(16)} ${String(count).padStart(6)} ${((100 * count) / cases.length).toFixed(1).padStart(6)}%`,
    )
}

const GATE_OPTIONS: Options = {
  accessors: true,
  attributes: true,
  inherited: true,
  nodes: 6,
  reorder: true,
  same: true,
}

/** The seeded batch `check-lean.ts` runs: every difference of `reconcile`, getter counts
 * included, and of `produce` or `snapshot` fails. */
export async function checkSpecGate(oracle: Oracle): Promise<void> {
  const reconciled = await checkSpec(reconcileCheck, oracle, seeds(1500), GATE_OPTIONS)
  assert.deepEqual(
    reconciled.reports,
    [],
    `Spec reconcile: ${reconciled.reports.length} differences`,
  )
  writesMode = true
  const written = await checkSpec(reconcileCheck, oracle, seeds(1500), GATE_OPTIONS)
  assert.deepEqual(written.reports, [], `Spec writes: ${written.reports.length} differences`)
  // Hazards: more accessors and dropping setters below the root, also through the recording
  // proxies, so demotion passes are common.
  const hazardous = await checkSpec(reconcileCheck, oracle, seeds(3000), {
    ...GATE_OPTIONS,
    hazards: true,
  })
  assert.deepEqual(hazardous.reports, [], `Spec hazards: ${hazardous.reports.length} differences`)
  // Buffers and views beside the other kinds, also through the recording proxies.
  const binary: Options = { ...GATE_OPTIONS, binary: true }
  const binaryReconciled = await checkSpec(reconcileCheck, oracle, seeds(1500), binary)
  writesMode = false
  assert.deepEqual(
    binaryReconciled.reports,
    [],
    `Spec binary reconcile: ${binaryReconciled.reports.length} differences`,
  )
  const produced = await checkSpec(produceCheck, oracle, seeds(1500), GATE_OPTIONS)
  assert.deepEqual(produced.reports, [], `Spec produce: ${produced.reports.length} differences`)
  const binaryProduced = await checkSpec(produceCheck, oracle, seeds(1500), binary)
  assert.deepEqual(
    binaryProduced.reports,
    [],
    `Spec binary produce: ${binaryProduced.reports.length} differences`,
  )
  const copied = await checkSpec(snapshotCheck, oracle, seeds(500), GATE_OPTIONS)
  assert.deepEqual(copied.reports, [], `Spec snapshot: ${copied.reports.length} differences`)
  const binaryCopied = await checkSpec(snapshotCheck, oracle, seeds(500), binary)
  assert.deepEqual(
    binaryCopied.reports,
    [],
    `Spec binary snapshot: ${binaryCopied.reports.length} differences`,
  )
  console.log(
    `Spec bridge: reconcile ${reconciled.cases} cases (${summary(reconciled.reports)}), ${written.cases} through recording proxies (${summary(written.reports)}), ${hazardous.cases} with hazards (${summary(hazardous.reports)}), ${binaryReconciled.cases} with buffers and views (${summary(binaryReconciled.reports)}); produce ${produced.cases} cases (${summary(produced.reports)}), ${binaryProduced.cases} with buffers and views (${summary(binaryProduced.reports)}); snapshot ${copied.cases} cases (${summary(copied.reports)}), ${binaryCopied.cases} with buffers and views (${summary(binaryCopied.reports)})`,
  )
}

/** Shows one case, the reference's outcome and the comparison. */
async function dump<T>(
  check: Check<T>,
  oracle: Oracle,
  seed: number,
  options: Options,
): Promise<void> {
  const c = check.generate(seed, options)
  console.log(check.show(c))
  const [outcome] = await ask(oracle, [check.request(c)])
  console.log(`reference ${stable(outcome)}`)
  for (const r of check.compare(seed, c, outcome)) console.log(`${r.kind}: ${r.detail}`)
}

/** Prints the first report of each kind, and the first five result differences. */
function show(reports: readonly Report[]): void {
  const shown = new Map<string, number>()
  const limit = (kind: Report['kind']): number => (kind === 'result' ? 5 : 1)
  for (const r of reports) {
    const count = shown.get(r.kind) ?? 0
    shown.set(r.kind, count + 1)
    if (count < limit(r.kind)) console.log(`--- seed ${r.seed} ${r.kind}\n${r.detail}`)
  }
}

async function batch<T>(
  check: Check<T>,
  oracle: Oracle,
  from: number,
  count: number,
  options: Options,
  strict: boolean,
): Promise<void> {
  const list = Array.from({ length: count }, (_, index) => from + index)
  const { cases, reports } = await checkSpec(check, oracle, list, options)
  console.log(`cases ${cases}; reports ${reports.length}; ${summary(reports)}`)
  show(reports)
  if (strict && reports.some((r) => r.kind !== 'getters')) process.exitCode = 1
}

if (process.argv[1]?.endsWith('lean-spec-bridge.ts')) {
  const { values } = parseArgs({
    allowNegative: true,
    options: {
      accessors: { default: true, type: 'boolean' },
      attributes: { default: true, type: 'boolean' },
      binary: { default: false, type: 'boolean' },
      dump: { type: 'string' },
      features: { default: false, type: 'boolean' },
      from: { default: '1', type: 'string' },
      hazards: { default: false, type: 'boolean' },
      inherited: { default: true, type: 'boolean' },
      nodes: { default: '6', type: 'string' },
      op: { default: 'reconcile', type: 'string' },
      reorder: { default: true, type: 'boolean' },
      same: { default: true, type: 'boolean' },
      seeds: { default: '200', type: 'string' },
      strict: { default: false, type: 'boolean' },
      writes: { default: false, type: 'boolean' },
    },
  })
  writesMode = values.writes
  const { startOracle } = await import('./lean-oracle')
  const oracle = await startOracle()
  try {
    const options: Options = {
      accessors: values.accessors,
      attributes: values.attributes,
      binary: values.binary,
      hazards: values.hazards,
      inherited: values.inherited,
      nodes: Number(values.nodes),
      reorder: values.reorder,
      same: values.same,
    }
    assert.ok(values.op in checks, `unknown operation ${values.op}`)
    const check = checks[values.op as keyof typeof checks] as Check<unknown>
    if (values.features) await features(oracle.run, seeds(Number(values.seeds)), options)
    else if (values.dump === undefined)
      await batch(
        check,
        oracle.run,
        Number(values.from),
        Number(values.seeds),
        options,
        values.strict,
      )
    else await dump(check, oracle.run, Number(values.dump), options)
  } finally {
    await oracle.close()
  }
}
