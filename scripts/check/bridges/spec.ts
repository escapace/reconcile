// Random differential bridge for the `Spec` family: generates graphs, runs the production
// runtime on real objects built from them, recaptures the result as a graph (identities, values,
// descriptors, prototypes, extensibility) and compares it with the Lean reference model's result
// on the same case, the getter counts of every current object and of every object only `next`
// holds included. A rejection must have the reference's reason: `PublicationWouldChangeNext` exactly
// when the reference's decision would change `next` (`changesNext`). Whatever the outcome, `next`
// must read back after the call with the identities and contents it had before. Every `reconcile`
// batch also checks fixed cases, some of shapes the random graphs almost never produce: the
// examples of `Spec.KeepsNext`, a walk that reaches a root in a call that succeeds, and objects
// that `next` holds at their own node. A standalone batch fails on any difference.
//
// The round trip runs `serialize`, JSON text and `deserialize` on the graphs restricted to what
// `serialize` accepts and compares the restored value with the reference's `snapshot`.
//
// Standalone: pnpm exec tsx scripts/check/bridges/spec.ts
//   [--op reconcile|produce|snapshot|roundtrip]
//   [--seeds N] [--from S] [--dump SEED] [--writes] [--hazards] [--binary] [--getters]
//   [--features] [--no-same] [--no-reorder] [--no-accessors] [--no-attributes] [--no-inherited]
//   [--nodes N]
// --getters adds accessors to the objects only `next` holds; --dump SEED shows that case, the
// reference's outcome and each difference; --features prints how often each feature occurs among
// the `reconcile` cases instead of comparing them.
import assert from 'node:assert/strict'
import { parseArgs } from 'node:util'
import {
  deserialize,
  isReconcileError,
  produce,
  reconcile,
  requiredMaxBytes,
  serialize,
  snapshot,
} from '../../../src/index'
import type { Oracle } from '../oracle'
import {
  atoms,
  construct,
  materialize,
  materializeClasses,
  materializeNext,
  primitiveToJs,
  prototypeIndex,
  setterStores,
  toJs,
  type Counters,
  type Resolve,
} from '../fixtures/spec-realize'
import {
  byKind,
  GATE_OPTIONS,
  genCase,
  genProduceCase,
  isHole,
  isReference,
  mapReferences,
  REGRESSION_SEEDS,
  seedRange,
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
  valuesOf,
} from '../fixtures/spec-generator'

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
export interface Outcome {
  nodes: GraphNode[]
  ok: boolean
  origins: Array<number | null>
  root: Value
  /** Getter counts of current objects after `next` is read, as `[current index, [key, count]]`,
   * Lean's nested pairs; `reconcile` only. */
  gets?: Array<[number, [string, number]]>
  /** Getter counts of current objects while `next` is read, labelled like `gets`. */
  nextGets?: Array<[number, [string, number]]>
  /** Getter counts of the objects only `next` holds, as `[next index, [key, count]]`. */
  freshGets?: Array<[number, [string, number]]>
  /** 0 when the call is rejected before any write; `reconcile` only. */
  passes?: number
  /** Whether the call is rejected because its decision would change `next`; `reconcile` only. */
  changesNext?: boolean
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

export interface Report {
  detail: string
  kind:
    | 'attributes'
    | 'current-changed'
    | 'error'
    | 'getters'
    | 'next-changed'
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

interface Attempt {
  /** Whether the rejection is `PublicationWouldChangeNext`. */
  changesNext: boolean
  rejected: boolean
  error?: unknown
  result?: unknown
}

/** The reconcile errors that reject a publication, with whether each is the `next` rule's. */
const REJECTIONS = new Map([
  ['PublicationRejected', false],
  ['PublicationWouldChangeNext', true],
])

/** Runs `operation`; a rejected publication is a status, any other error is returned. */
function attempt(operation: () => unknown): Attempt {
  try {
    return { changesNext: false, rejected: false, result: operation() }
  } catch (error) {
    const changesNext = isReconcileError(error) ? REJECTIONS.get(error.cause.type) : undefined
    return changesNext === undefined
      ? { changesNext: false, error, rejected: false }
      : { changesNext, rejected: true }
  }
}

/** The reason a rejection names, as the reference reports it. */
const reason = (changesNext: boolean | undefined): string =>
  changesNext === true ? 'would change next' : 'rejected'

/** The getter counts the runtime made so far, labelled `<prefix> <index>.<key>` by the object's
 * index in `objects`; then resets the counts. */
function getterCounts(
  counters: Counters,
  objects: readonly object[],
  prefix: string,
): Map<string, number> {
  const counts = new Map<string, number>()
  for (const [o, byKey] of counters)
    for (const [k, count] of byKey) {
      counts.set(`${prefix} ${objects.indexOf(o)}.${k}`, count.get)
      count.get = 0
    }
  return counts
}

type Counts = Array<[number, [string, number]]>

/** Counts labelled like `getterCounts`, the counts of each label added up. */
function labelled(prefix: string, ...lists: Array<Counts | undefined>): Map<string, number> {
  const counts = new Map<string, number>()
  for (const [index, [k, n]] of lists.flatMap((list) => list ?? [])) {
    const label = `${prefix} ${index}.${k}`
    counts.set(label, (counts.get(label) ?? 0) + n)
  }
  return counts
}

/** The getter counts of current objects the reference expects: after `next` is read, and while
 * it is read, for the objects `next` holds. */
const wantedGets = (expected: Outcome): Map<string, number> =>
  labelled('current', expected.gets, expected.nextGets)

/** The getter counts of the objects only `next` holds the reference expects. */
const wantedFreshGets = (expected: Outcome): Map<string, number> =>
  labelled('next', expected.freshGets)

/** Reports a setter of an object only `next` holds that ran: `reconcile` never writes to `next`. */
function reportNextSetters(seed: number, counters: Counters, next: readonly object[]): Report[] {
  const reports: Report[] = []
  for (const [o, byKey] of counters)
    for (const [key, count] of byKey)
      if (count.set > 0)
        reports.push({
          detail: `next ${next.indexOf(o)}.${key}: ${count.set} sets`,
          kind: 'writes',
          seed,
        })
  return reports
}

/** Getter counts for accessor slots, which must agree both ways. */
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

/** How a runtime rejection, `PublicationWouldChangeNext` when `changesNext`, differs from the
 * reference's outcome: the reference succeeds or rejects for another reason. */
function rejectionMismatch(expected: Outcome, changesNext: boolean): string | undefined {
  if (expected.ok) return `runtime ${reason(changesNext)}; reference succeeds`
  return changesNext === (expected.changesNext === true)
    ? undefined
    : `runtime ${reason(changesNext)}; reference ${reason(expected.changesNext)}`
}

/** Reports a runtime rejection against the reference: whether the reference succeeds or rejects
 * for another reason, and whether `current` changed before a rejection the reference decides
 * before any write. */
function reportRejection(
  seed: number,
  expected: Outcome,
  changesNext: boolean,
  changed: boolean,
): Report[] {
  const reports: Report[] = []
  const mismatch = rejectionMismatch(expected, changesNext)
  if (mismatch !== undefined) reports.push({ detail: mismatch, kind: 'rejection', seed })
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
  const nextCounters: Counters = new Map()
  const writes: Writes = new Map()
  const armed = { on: false }
  const wrap = (o: object, index: number): object =>
    writesMode && recorded(c.cur.nodes[index]) ? recordingProxy(o, writes, armed) : o
  const prototypeCounters: Counters = new Map()
  const classes = materializeClasses(c.classes, prototypeCounters)
  classIndex = new Map(classes.map((p, index) => [p, index]))
  const current = materialize(c.cur, counters, undefined, wrap, classes)
  const next = materializeNext(c, current, classes, nextCounters)
  const before = stable(recapture(current[0], current))
  const nextRoot = toJs(c.next.root, next)
  // Every object `next` reaches, numbered by node and then as a current object.
  const known = [...next, ...current]
  const nextBefore = stable(recapture(nextRoot, known))
  getterCounts(counters, current, 'current')
  getterCounts(nextCounters, next, 'next')
  armed.on = true
  const run = attempt(() => reconcile(toJs(c.cur.root, current), nextRoot))
  armed.on = false
  const gets = getterCounts(counters, current, 'current')
  const freshGets = getterCounts(nextCounters, next, 'next')
  const reports = reconcileReports(seed, c, expected, run, current, before, gets, writes)
  // `next` is read in full whether the call succeeds or not.
  if (!('error' in run)) reportGetters(seed, freshGets, wantedFreshGets(expected), reports)
  // `next` keeps its identities and contents whatever the outcome.
  const nextAfter = stable(recapture(nextRoot, known))
  if (nextAfter !== nextBefore)
    reports.push({
      detail: `${run.rejected ? reason(run.changesNext) : 'succeeded'}\nbefore ${nextBefore}\nafter  ${nextAfter}`,
      kind: 'next-changed',
      seed,
    })
  classIndex = prototypeIndex
  return [
    ...reports,
    ...reportNextSetters(seed, nextCounters, next),
    ...prototypeReports(seed, prototypeCounters, classes),
  ]
}

/** The reports of a run's outcome against the reference's. */
function reconcileReports(
  seed: number,
  c: Case,
  expected: Outcome,
  run: Attempt,
  current: readonly object[],
  before: string,
  gets: ReadonlyMap<string, number>,
  writes: Writes,
): Report[] {
  if ('error' in run) return [errorReport(seed, run.error)]
  if (run.rejected)
    return reportRejection(
      seed,
      expected,
      run.changesNext,
      stable(recapture(current[0], current)) !== before,
    )
  if (!expected.ok)
    return [
      {
        detail: `reference ${reason(expected.changesNext)}; runtime succeeded`,
        kind: 'rejection',
        seed,
      },
    ]
  const reports: Report[] = []
  compareCaptured(seed, recapture(run.result, current), expected, reports)
  reportGetters(seed, gets, wantedGets(expected), reports)
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
export interface Check<T> {
  compare: (seed: number, c: T, expected: Outcome) => Report[]
  generate: (seed: number, options: Options) => T
  request: (c: T) => object
  show: (c: T) => string
}

export const reconcileCheck: Check<Case> = {
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

export const produceCheck: Check<Recipe> = {
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

export const snapshotCheck: Check<Graph> = {
  compare: (seed, graph, expected) =>
    compareCopy(seed, graph, expected, (current) => snapshot(toJs(graph.root, current))),
  generate: (seed, options) => genCase(seed, options).cur,
  request: (graph) => ({ cur: graph, op: 'snapshot' }),
  show: (graph) => `cur ${stable(graph)}`,
}

/** A value `serialize` accepts in place of an atom, which stands for a function: a string no
 * generated value has. */
const serializableValue = (v: Value): Value =>
  typeof v === 'object' && v !== null && 'atom' in v ? `f${v.atom}` : v

/** A slot as `serialize` accepts it: enumerable, with its other attributes, or its accessor. */
const serializableSlot = (s: Slot): Slot =>
  'v' in s
    ? { a: [s.a[0], true, s.a[2]], v: serializableValue(s.v) }
    : { ...s, e: true, get: serializableValue(s.get) }

/** Each node as `serialize` accepts it: atoms replaced, every property enumerable, a class
 * prototype replaced with `Object.prototype` and a resizable buffer fixed in length. */
const serializables: ByKind<[], GraphNode> = {
  array: (n) => ({
    ...n,
    entries: n.entries.map((entry) => (isHole(entry) ? entry : serializableValue(entry))),
  }),
  buffer: (n) => ({ ...n, max: null }),
  date: (n) => n,
  map: (n) => ({
    ...n,
    entries: n.entries.map(([k, v]): [Value, Value] => [
      serializableValue(k),
      serializableValue(v),
    ]),
  }),
  object: (n) => ({
    ...n,
    fields: n.fields.map(([k, slot]): [string, Slot] => [k, serializableSlot(slot)]),
    proto: n.proto === 'null' ? 'null' : 'object',
  }),
  set: (n) => ({ ...n, members: n.members.map(serializableValue) }),
  view: (n) => n,
}

/** A graph restricted to what `serialize` accepts. Read-only properties, accessors, integrity
 * levels, holes, sharing and cycles stay. */
const serializableGraph = (graph: Graph): Graph => ({
  nodes: graph.nodes.map((node) => byKind(serializables, node)),
  root: serializableValue(graph.root),
})

/** The values of node `id` in the order `serialize` visits them, each with the getter, as
 * `<node>.<key>`, that runs as its key is read: none, or one for an object's accessor. */
function visits(node: GraphNode, id: number): Array<[getters: string[], value: Value]> {
  if (node.kind !== 'object') return byKind(valuesOf, node).map((child) => [[], child])
  return node.fields.map(([key, slot]) => ['get' in slot ? [`${id}.${key}`] : [], slotValue(slot)])
}

/** The getter runs `serialize` makes, as `<node>.<key>`: depth first from the root, each node's
 * values in order, a getter run as its key is read, before its value is visited. */
function getterOrder(graph: Graph): string[] {
  const seen = new Set<number>()
  const order: string[] = []
  const visit = (v: Value): void => {
    if (!isReference(v) || seen.has(v.ref)) return
    seen.add(v.ref)
    for (const [getters, child] of visits(graph.nodes[v.ref], v.ref)) {
      order.push(...getters)
      visit(child)
    }
  }
  visit(graph.root)
  return order
}

/** Serializes `value`, writes and parses the JSON text, and deserializes it with the size
 * `requiredMaxBytes` measures; `refused` is whether one byte less is refused as too large. */
function roundTrip(value: unknown): { refused: boolean; result: unknown } {
  const text = JSON.stringify(serialize(value))
  const maxBytes = requiredMaxBytes(JSON.parse(text), { maxBytes: Infinity })
  let refused = false
  try {
    deserialize(JSON.parse(text), { maxBytes: maxBytes - 1 })
  } catch (error) {
    refused = isReconcileError(error) && error.cause.type === 'DeserializeLimitExceeded'
  }
  return { refused, result: deserialize(JSON.parse(text), { maxBytes }) }
}

/** Whether an accessor of the source ran other than as one getter call. */
const misread = (count: { get: number; set: number }): boolean => count.get !== 1 || count.set !== 0

/** Reports each getter of the source that did not run exactly once, and each setter that ran. */
function sourceAccessorReports(
  seed: number,
  counters: Counters,
  objects: readonly object[],
): Report[] {
  const reports: Report[] = []
  for (const [o, byKey] of counters)
    for (const [key, count] of byKey)
      if (misread(count))
        reports.push({
          detail: `${objects.indexOf(o)}.${key}: ${count.get} gets, ${count.set} sets`,
          kind: 'getters',
          seed,
        })
  return reports
}

/** Reports each getter of the source that did not run exactly once, each setter that ran, and a
 * getter order other than depth first. */
function reportSourceReads(
  seed: number,
  counters: Counters,
  objects: readonly object[],
  calls: readonly string[],
  graph: Graph,
): Report[] {
  const reports = sourceAccessorReports(seed, counters, objects)
  const order = getterOrder(graph).join(' ')
  if (calls.join(' ') !== order)
    reports.push({ detail: `runtime ${calls.join(' ')}\nmodel ${order}`, kind: 'getters', seed })
  return reports
}

/** Sets every getter count to zero. */
function resetGets(counters: Counters): void {
  for (const byKey of counters.values()) for (const count of byKey.values()) count.get = 0
}

/** Runs one graph through `serialize`, JSON text and `deserialize`, and compares the restored
 * value with the reference's `snapshot` of the graph: on the graphs `serialize` accepts, the round
 * trip restores what `snapshot` copies, every object new. */
function compareRoundTrip(seed: number, graph: Graph, expected: Outcome): Report[] {
  const counters: Counters = new Map()
  const calls: string[] = []
  const objects: object[] = materialize(
    graph,
    counters,
    undefined,
    undefined,
    undefined,
    (o, key) => calls.push(`${objects.indexOf(o)}.${key}`),
  )
  const value = toJs(graph.root, objects)
  const before = stable(recapture(value, objects))
  resetGets(counters)
  calls.length = 0
  const run = attempt(() => roundTrip(value))
  if ('error' in run) return [errorReport(seed, run.error)]
  const reports = reportSourceReads(seed, counters, objects, calls, graph)
  const { refused, result } = run.result as ReturnType<typeof roundTrip>
  if (!refused)
    reports.push({ detail: 'one byte below the size accepted', kind: 'rejection', seed })
  if (stable(recapture(value, objects)) !== before)
    reports.push({ detail: 'the source changed', kind: 'current-changed', seed })
  compareCaptured(seed, recapture(result, objects), expected, reports)
  return reports
}

const toNode = (node: number): Value => ({ ref: node })

/** A plain object of writable, enumerable and configurable data properties, as `Spec.KeepsNext`
 * builds its examples. */
const plainNode = (fields: Array<[string, Value]>): GraphNode => ({
  extensible: true,
  fields: fields.map(([key, v]): [string, Slot] => [key, { a: [true, true, true], v }]),
  kind: 'object',
  proto: 'object',
})

/** An object whose `key` is a getter without a setter that reads `value`. */
const getterNode = (key: string, value: Value): GraphNode => ({
  extensible: true,
  fields: [[key, { c: true, e: true, get: value, set: null }]],
  kind: 'object',
  proto: 'object',
})

/** A case of two graphs rooted at node 0. */
const exampleCase = (
  current: GraphNode[],
  next: GraphNode[],
  same: Array<number | null>,
): Case => ({
  classes: [],
  cur: { nodes: current, root: toNode(0) },
  next: { nodes: next, root: toNode(0) },
  same,
})

/** A fixed case, with the outcome its theorem or design states. */
interface Example {
  readonly c: Case
  readonly name: string
  readonly outcome: { changesNext: boolean; ok: boolean; passes?: number }
}

const WOULD_CHANGE_NEXT = { changesNext: true, ok: false, passes: 0 }

/** A root holding node 1 at `a` and node 2 at `b`. */
const AB = plainNode([
  ['a', toNode(1)],
  ['b', toNode(2)],
])

/** The object of `walkReachesRoot` whose walk reaches the root of `next`: its read-only,
 * non-configurable `up` holds node `up`, between nodes `a` and `b`. */
const walker = (a: number, up: number, b: number): NodeOf<'object'> => ({
  extensible: true,
  fields: [
    ['a', { a: [true, true, true], v: toNode(a) }],
    ['up', { a: [false, true, false], v: toNode(up) }],
    ['b', { a: [true, true, true], v: toNode(b) }],
  ],
  kind: 'object',
  proto: 'object',
})

/** `node` with a getter `g` without a setter that reads 7 after its fields. */
const withGetter = (node: NodeOf<'object'>): GraphNode => ({
  ...node,
  fields: [...node.fields, ['g', { c: true, e: true, get: 7, set: null }]],
})

/** A `Map` value that `next` holds at its own node and whose slot `c`, made by `slot`, holds an
 * object at the node whose first candidate is another object, the root's `x`. */
const ownSlotCase = (slot: (value: Value) => Slot): Case => {
  const holder = (child: number): GraphNode => ({
    extensible: true,
    fields: [['c', slot(toNode(child))]],
    kind: 'object',
    proto: 'object',
  })
  const root = plainNode([
    ['x', toNode(1)],
    ['m', toNode(2)],
  ])
  const map: GraphNode = { entries: [[1, toNode(3)]], kind: 'map' }
  return exampleCase(
    [root, plainNode([['v', 2]]), map, holder(4), plainNode([['v', 1]])],
    [root, plainNode([['v', 1]]), map, holder(1)],
    [null, 4, null, 3],
  )
}

/** The examples of `Spec.KeepsNext`: a counterexample for each clause of the rule (`swap`,
 * `mapChild`), its conservative case (`equalCopy`), a rejection after one pass (`laterPass`), an
 * object in place (`inPlace`) and `next` holding `current` below a new root (`rootCycle`). Then a
 * call that succeeds although the walk of an object in place reaches the root of `next`, which is
 * an object of `current`: the object cannot take the root's target at its read-only `up`, so it is
 * copied, and nothing `next` holds is kept elsewhere (`walkReachesRoot`). Every other walk that
 * reaches a root rejects the call, so this case alone shows the order of the walk's reads. Last,
 * calls with an object of `current` that `next` holds at its own node. In three that succeed, the
 * object is a candidate both at the node it is, where it is not read as `current`, and at another
 * node, where it is: the object is that walker, which capture aligns first at its own node and
 * again at the other (`ownNodeInCapture`), or aligns at its own node only before discovery walks it
 * as a `Map` value at the other (`ownNodeAlignedOnce`), or a `Map` value that discovery walks first
 * at its own node (`ownNodeInDiscovery`). Each runs its getter once as `current`. In the last two,
 * a `Map` value at its own node holds at `c` an object whose node the root's `x` first offers
 * another object: a getter without a setter at `c` is fixed and requires the object, so the call
 * succeeds (`ownNodeFixedSlot`); a writable, non-configurable `c` is not, so the node keeps the
 * other object and the call is rejected (`ownNodeWritableSlot`). */
const EXAMPLES: readonly Example[] = [
  {
    c: exampleCase(
      [AB, plainNode([['v', 1]]), plainNode([['v', 2]])],
      [AB, plainNode([['v', 2]]), plainNode([['v', 1]])],
      [null, 2, 1],
    ),
    name: 'swap',
    outcome: WOULD_CHANGE_NEXT,
  },
  {
    c: exampleCase(
      [
        plainNode([
          ['p', toNode(1)],
          ['m', toNode(2)],
        ]),
        plainNode([['v', 1]]),
        { entries: [[1, toNode(3)]], kind: 'map' },
        plainNode([['c', toNode(4)]]),
        plainNode([['v', 2]]),
      ],
      [
        plainNode([
          ['p', toNode(1)],
          ['m', toNode(2)],
        ]),
        plainNode([['v', 2]]),
        { entries: [[1, toNode(3)]], kind: 'map' },
        plainNode([['c', toNode(1)]]),
      ],
      [null, 4, null, 3],
    ),
    name: 'mapChild',
    outcome: WOULD_CHANGE_NEXT,
  },
  {
    c: exampleCase(
      [AB, plainNode([['v', 1]]), plainNode([['v', 2]])],
      [AB, plainNode([['v', 2]]), plainNode([['v', 2]])],
      [null, 2, null],
    ),
    name: 'equalCopy',
    outcome: WOULD_CHANGE_NEXT,
  },
  {
    c: exampleCase(
      [
        AB,
        {
          extensible: true,
          fields: [['s', { c: true, e: true, get: 1, set: false }]],
          kind: 'object',
          proto: 'object',
        },
        plainNode([['s', 1]]),
      ],
      [
        plainNode([
          ['a', toNode(1)],
          ['b', toNode(1)],
          ['c', toNode(2)],
        ]),
        plainNode([['s', 2]]),
        plainNode([['s', 1]]),
      ],
      [null, null, 2],
    ),
    name: 'laterPass',
    outcome: { changesNext: true, ok: false, passes: 2 },
  },
  {
    c: exampleCase(
      [plainNode([['a', toNode(1)]]), plainNode([['v', 1]])],
      [
        plainNode([
          ['a', toNode(1)],
          ['n', 1],
        ]),
        plainNode([['v', 1]]),
      ],
      [null, 1],
    ),
    name: 'inPlace',
    outcome: { changesNext: false, ok: true },
  },
  {
    c: exampleCase(
      [plainNode([['a', toNode(1)]]), plainNode([['up', toNode(0)]])],
      [
        plainNode([
          ['a', toNode(1)],
          ['n', 1],
        ]),
        plainNode([['up', toNode(2)]]),
        plainNode([['a', toNode(1)]]),
      ],
      [null, 1, 0],
    ),
    name: 'rootCycle',
    outcome: WOULD_CHANGE_NEXT,
  },
  {
    c: {
      ...exampleCase(
        [
          plainNode([
            ['k', toNode(2)],
            ['j', toNode(1)],
          ]),
          plainNode([['k', toNode(2)]]),
          walker(3, 1, 4),
          getterNode('g', 1),
          getterNode('h', 2),
        ],
        [plainNode([['k', toNode(1)]]), walker(2, 0, 3), getterNode('g', 1), getterNode('h', 2)],
        [1, 2, 3, 4],
      ),
    },
    name: 'walkReachesRoot',
    outcome: { changesNext: false, ok: true },
  },
  {
    c: exampleCase(
      [
        plainNode([
          ['k', toNode(2)],
          ['j', toNode(1)],
          ['q', toNode(2)],
        ]),
        plainNode([
          ['k', toNode(2)],
          ['q', toNode(5)],
        ]),
        withGetter(walker(3, 1, 4)),
        getterNode('g', 1),
        getterNode('h', 2),
        plainNode([['g', 5]]),
      ],
      [
        plainNode([
          ['k', toNode(1)],
          ['q', toNode(4)],
        ]),
        withGetter(walker(2, 0, 3)),
        getterNode('g', 1),
        getterNode('h', 2),
        plainNode([['g', 5]]),
      ],
      [1, 2, 3, 4, 5],
    ),
    name: 'ownNodeInCapture',
    outcome: { changesNext: false, ok: true },
  },
  {
    c: exampleCase(
      [
        plainNode([['m', toNode(1)]]),
        {
          entries: [
            [1, toNode(2)],
            [2, toNode(2)],
          ],
          kind: 'map',
        },
        getterNode('g', 1),
      ],
      [
        plainNode([['m', toNode(1)]]),
        {
          entries: [
            [1, toNode(2)],
            [2, toNode(3)],
          ],
          kind: 'map',
        },
        getterNode('g', 1),
        plainNode([['g', 5]]),
      ],
      [null, null, 2, null],
    ),
    name: 'ownNodeInDiscovery',
    outcome: { changesNext: false, ok: true },
  },
  {
    c: exampleCase(
      [
        plainNode([
          ['k', toNode(2)],
          ['j', toNode(1)],
          ['q', toNode(6)],
        ]),
        plainNode([
          ['k', toNode(2)],
          ['q', toNode(7)],
        ]),
        withGetter(walker(3, 1, 4)),
        getterNode('g', 1),
        getterNode('h', 2),
        plainNode([['g', 5]]),
        { entries: [[1, toNode(2)]], kind: 'map' },
        { entries: [[1, toNode(5)]], kind: 'map' },
      ],
      [
        plainNode([
          ['k', toNode(1)],
          ['q', toNode(5)],
        ]),
        withGetter(walker(2, 0, 3)),
        getterNode('g', 1),
        getterNode('h', 2),
        plainNode([['g', 5]]),
        { entries: [[1, toNode(4)]], kind: 'map' },
      ],
      [1, 2, 3, 4, 5, 7],
    ),
    name: 'ownNodeAlignedOnce',
    outcome: { changesNext: false, ok: true },
  },
  {
    c: ownSlotCase((get) => ({ c: true, e: true, get, set: null })),
    name: 'ownNodeFixedSlot',
    outcome: { changesNext: false, ok: true },
  },
  {
    c: ownSlotCase((v) => ({ a: [true, true, false], v })),
    name: 'ownNodeWritableSlot',
    outcome: WOULD_CHANGE_NEXT,
  },
]

/** Whether an outcome is the one stated, whose pass count, when it states one, included. */
const statedOutcome = (stated: Example['outcome'], got: Example['outcome']): boolean =>
  got.ok === stated.ok &&
  got.changesNext === stated.changesNext &&
  (stated.passes === undefined || got.passes === stated.passes)

/** Reports an example whose reference outcome is not the one its theorem states. */
function exampleReports(example: Example, seed: number, outcome: Outcome): Report[] {
  const got = { changesNext: outcome.changesNext === true, ok: outcome.ok, passes: outcome.passes }
  return statedOutcome(example.outcome, got)
    ? []
    : [
        {
          detail: `${example.name}: reference ${stable(got)}, theorem ${stable(example.outcome)}`,
          kind: 'rejection',
          seed,
        },
      ]
}

/** Compares the examples in each mode, after checking the reference's outcome of each against the
 * one it states; a report's seed is minus one minus the example's index. */
async function checkExamples(oracle: Oracle, modes: readonly boolean[]): Promise<Report[][]> {
  const cases = EXAMPLES.map((example) => example.c)
  const seedsOf = cases.map((_, index) => -1 - index)
  const outcomes = await ask(oracle, cases.map(reconcileCheck.request))
  const stated = EXAMPLES.flatMap((example, index) =>
    exampleReports(example, seedsOf[index], outcomes[index]),
  )
  const compared = await compareAll(reconcileCheck, oracle, cases, seedsOf, modes)
  return compared.map((list) => [...stated, ...list])
}

const roundTripCheck: Check<Graph> = {
  compare: compareRoundTrip,
  generate: (seed, options) => serializableGraph(genCase(seed, options).cur),
  request: (graph) => ({ cur: graph, op: 'snapshot' }),
  show: (graph) => `cur ${stable(graph)}`,
}

const checks = {
  produce: produceCheck,
  reconcile: reconcileCheck,
  roundtrip: roundTripCheck,
  snapshot: snapshotCheck,
}

/** Asks the oracle for the outcomes of `requests`, one per request. */
async function ask(oracle: Oracle, requests: readonly object[]): Promise<Outcome[]> {
  const input = JSON.stringify(requests)
  const output = (await oracle('Spec', { input, maxBuffer: 64 * 1024 * 1024 })).trim()
  const outcomes = JSON.parse(output) as Outcome[]
  assert.equal(outcomes.length, requests.length)
  return outcomes
}

/** Asks the oracle once for the outcomes of `cases` and compares each in every mode: plain, or
 * `reconcile` through recording proxies where the mode is `true`. A report is filed under its
 * case's id, and each mode's reports are listed apart. */
async function compareAll<T>(
  check: Check<T>,
  oracle: Oracle,
  cases: readonly T[],
  ids: readonly number[],
  modes: readonly boolean[],
): Promise<Report[][]> {
  const outcomes = await ask(oracle, cases.map(check.request))
  const previous = writesMode
  try {
    return modes.map((writes) => {
      writesMode = writes
      return cases.flatMap((c, index) => check.compare(ids[index], c, outcomes[index]))
    })
  } finally {
    writesMode = previous
  }
}

/** Generates cases from `seeds`, asks the oracle once for all of them and compares in each mode. */
async function checkSpec<T>(
  check: Check<T>,
  oracle: Oracle,
  seeds: readonly number[],
  options: Options,
  modes: readonly boolean[] = [writesMode],
): Promise<{ cases: number; reports: Report[][] }> {
  const cases = seeds.map((seed) => check.generate(seed, options))
  return { cases: cases.length, reports: await compareAll(check, oracle, cases, seeds, modes) }
}

/** Compares the given cases with the reference in each mode, as `compareAll` does; a report's
 * seed is its case's index. */
export async function checkCases<T>(
  check: Check<T>,
  oracle: Oracle,
  cases: readonly T[],
  modes: readonly boolean[] = [false],
): Promise<Report[][]> {
  return await compareAll(
    check,
    oracle,
    cases,
    cases.map((_, index) => index),
    modes,
  )
}

/** The seeds `1` to `count`. */
const seeds = (count: number): number[] => seedRange(1, count)

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
  ['nextHoldsRoot', c.same.includes(0)],
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
  ['changesNext', outcome.changesNext === true],
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

/** The seeded batch `scripts/check/lean.ts` runs: every difference of `reconcile`, getter counts
 * included, and of `produce` or `snapshot` fails. */
export async function checkSpecGate(oracle: Oracle): Promise<void> {
  const binary: Options = { ...GATE_OPTIONS, binary: true }
  // The default cases plain and through the recording proxies; hazards (more accessors and
  // dropping setters below the root, so demotion passes are common), buffers and views beside
  // the other kinds, and accessors on the objects only `next` holds through the proxies only.
  const summaries: string[] = []
  const gate = async <T>(
    name: string,
    check: Check<T>,
    count: number,
    options: Options,
    modes: boolean[],
    regressions: readonly number[] = [],
  ): Promise<void> => {
    const seedList = [...seeds(count), ...regressions]
    const { cases, reports } = await checkSpec(check, oracle, seedList, options, modes)
    reports.forEach((list, mode) => {
      const label = modes[mode] ? `${name} through recording proxies` : name
      assert.deepEqual(list, [], `Spec ${label}: ${list.length} differences`)
      summaries.push(`${label} ${cases} cases (${summary(list)})`)
    })
  }
  await gate('reconcile', reconcileCheck, 1500, GATE_OPTIONS, [false, true], REGRESSION_SEEDS.plain)
  const examples = await checkExamples(oracle, [false, true])
  examples.forEach((list, mode) => {
    const label = mode === 1 ? 'examples through recording proxies' : 'examples'
    assert.deepEqual(list, [], `Spec ${label}: ${list.length} differences`)
    summaries.push(`${label} ${EXAMPLES.length} cases (${summary(list)})`)
  })
  await gate(
    'reconcile with hazards',
    reconcileCheck,
    3000,
    { ...GATE_OPTIONS, hazards: true },
    [true],
    REGRESSION_SEEDS.hazards,
  )
  await gate('reconcile with buffers and views', reconcileCheck, 1500, binary, [true])
  await gate(
    'reconcile with accessors in next',
    reconcileCheck,
    1500,
    { ...GATE_OPTIONS, nextAccessors: true },
    [true],
  )
  await gate('produce', produceCheck, 1500, GATE_OPTIONS, [false])
  await gate('produce with buffers and views', produceCheck, 1500, binary, [false])
  await gate('snapshot', snapshotCheck, 500, GATE_OPTIONS, [false])
  await gate('snapshot with buffers and views', snapshotCheck, 500, binary, [false])
  await gate('round trip with buffers and views', roundTripCheck, 1500, binary, [false])
  console.log(`Spec bridge: ${summaries.join('; ')}`)
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
): Promise<void> {
  const {
    cases,
    reports: [found],
  } = await checkSpec(check, oracle, seedRange(from, count), options)
  // The examples are reconcile cases, which every reconcile batch checks too.
  const reconciles = check === (reconcileCheck as Check<unknown>)
  const examples = reconciles ? (await checkExamples(oracle, [writesMode]))[0] : []
  const reports = [...found, ...examples]
  const listed = reconciles ? EXAMPLES.length : 0
  console.log(
    `cases ${cases} and ${listed} examples; reports ${reports.length}; ${summary(reports)}`,
  )
  show(reports)
  if (reports.length > 0) process.exitCode = 1
}

if (process.argv[1]?.endsWith('scripts/check/bridges/spec.ts')) {
  const { values } = parseArgs({
    allowNegative: true,
    options: {
      accessors: { default: true, type: 'boolean' },
      attributes: { default: true, type: 'boolean' },
      binary: { default: false, type: 'boolean' },
      dump: { type: 'string' },
      features: { default: false, type: 'boolean' },
      from: { default: '1', type: 'string' },
      getters: { default: false, type: 'boolean' },
      hazards: { default: false, type: 'boolean' },
      inherited: { default: true, type: 'boolean' },
      nodes: { default: '6', type: 'string' },
      op: { default: 'reconcile', type: 'string' },
      reorder: { default: true, type: 'boolean' },
      same: { default: true, type: 'boolean' },
      seeds: { default: '200', type: 'string' },
      writes: { default: false, type: 'boolean' },
    },
  })
  writesMode = values.writes
  const { startOracle } = await import('../oracle')
  const oracle = await startOracle()
  try {
    const options: Options = {
      accessors: values.accessors,
      attributes: values.attributes,
      binary: values.binary,
      hazards: values.hazards,
      inherited: values.inherited,
      nextAccessors: values.getters,
      nodes: Number(values.nodes),
      reorder: values.reorder,
      same: values.same,
    }
    assert.ok(values.op in checks, `unknown operation ${values.op}`)
    const check = checks[values.op as keyof typeof checks] as Check<unknown>
    if (values.features) await features(oracle.run, seeds(Number(values.seeds)), options)
    else if (values.dump === undefined)
      await batch(check, oracle.run, Number(values.from), Number(values.seeds), options)
    else await dump(check, oracle.run, Number(values.dump), options)
  } finally {
    await oracle.close()
  }
}
