// Random differential bridge for the `Spec` family: generates graphs, runs the production
// runtime on real objects built from them, recaptures the result as a graph (identities, values,
// descriptors, prototypes, extensibility) and compares it with the Lean reference model's result
// on the same case. Getter counts are compared as a report.
//
// Standalone: pnpm exec tsx scripts/lean-spec-bridge.ts [--op reconcile|produce|snapshot]
//   [--seeds N] [--from S] [--strict] [--dump SEED] [--no-same] [--no-reorder] [--no-accessors]
//   [--no-attributes] [--nodes N]
import assert from 'node:assert/strict'
import { parseArgs } from 'node:util'
import { isReconcileError, produce, reconcile, snapshot } from '../src/index'
import type { Oracle } from './lean-oracle'
import {
  ATOMS,
  byKind,
  CLASSES,
  genCase,
  genProduceCase,
  isHole,
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
} from './spec-generator'

/** The prototypes of the model's classes. */
const prototypes = Array.from({ length: CLASSES }, (): object => ({}))
const prototypeIndex = new Map(prototypes.map((p, index) => [p, index]))
const atoms = Array.from({ length: ATOMS }, (_, index) => (): number => index)

/** Getter and setter calls per object and key, recorded by the accessors the bridge installs. */
type Counters = Map<object, Map<string, { get: number; set: number }>>
/** Whether an installed setter stores its value, by setter function. */
const setterStores = new WeakMap<object, boolean>()
type Accessor = Extract<Slot, { get: Value }>
type Resolve = (v: Value) => unknown

const primitiveToJs = (v: Exclude<Value, { ref: number }>): unknown =>
  v === null || typeof v !== 'object' ? v : 'undef' in v ? undefined : atoms[v.atom]

const toJs = (v: Value, objects: readonly object[]): unknown =>
  isReference(v) ? objects[v.ref] : primitiveToJs(v)

const prototypeOf = (prototype: NodeOf<'object'>['proto']): object | null =>
  prototype === 'object'
    ? Object.prototype
    : prototype === 'null'
      ? null
      : prototypes[prototype.cls]

const shells: ByKind<[], object> = {
  array: () => [],
  date: (node) => new Date(node.ms),
  map: () => new Map(),
  object: (node) => Object.create(prototypeOf(node.proto)) as object,
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

/** Builds the objects of a graph; `fixed(j)` supplies an existing object for node `j`. */
function materialize(
  graph: Graph,
  counters: Counters,
  fixed: (index: number) => object | undefined = () => undefined,
): object[] {
  const objects = graph.nodes.map((node, index) => fixed(index) ?? byKind(shells, node))
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

function prototypeLabel(o: object): NodeOf<'object'>['proto'] {
  const prototype = Object.getPrototypeOf(o) as object | null
  if (prototype === null) return 'null'
  if (prototype === Object.prototype) return 'object'
  const cls = prototypeIndex.get(prototype)
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
    | 'rejection'
    | 'result'
    | 'retention'
    | 'wrote-before-rejecting'
  seed: number
}

/** The values a node shows, without attributes, prototype or extensibility. */
const shapes: ByKind<[], unknown> = {
  array: (node) => ({ entries: node.entries, kind: node.kind }),
  date: (node) => node,
  map: (node) => node,
  object: (node) => ({
    fields: node.fields.map(([k, slot]) => [k, slotValue(slot)]),
    kind: node.kind,
  }),
  set: (node) => node,
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
function attempt(operation: () => unknown): {
  rejected: boolean
  error?: unknown
  result?: unknown
} {
  try {
    return { rejected: false, result: operation() }
  } catch (error) {
    const rejected = isReconcileError(error) && error.cause.type === 'PublicationRejected'
    return rejected ? { rejected } : { error, rejected }
  }
}

/** The getter counts the runtime made, labelled `<current index>.<key>`. */
function getterCounts(counters: Counters, current: readonly object[]): Map<string, number> {
  const counts = new Map<string, number>()
  for (const [o, byKey] of counters)
    for (const [k, count] of byKey) counts.set(`${current.indexOf(o)}.${k}`, count.get)
  return counts
}

/** The getter counts the reference expects, labelled like `getterCounts`. */
const wantedGets = (expected: Outcome): Map<string, number> =>
  new Map((expected.gets ?? []).map(([index, [k, n]]) => [`${index}.${k}`, n]))

/** Getter counts for accessor slots of current objects: a report, not a gate. */
function reportGetters(
  seed: number,
  counters: Counters,
  current: readonly object[],
  expected: Outcome,
  reports: Report[],
): void {
  const wanted = wantedGets(expected)
  for (const [label, n] of getterCounts(counters, current)) {
    const w = wanted.get(label) ?? 0
    if (n !== w)
      reports.push({ detail: `${label}: runtime ${n} reference ${w}`, kind: 'getters', seed })
  }
}

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

/** Runs one case through `reconcile` and compares with the reference outcome. */
function compareReconcile(seed: number, c: Case, expected: Outcome): Report[] {
  const counters: Counters = new Map()
  const current = materialize(c.cur, counters)
  const next = materialize(c.next, new Map(), (index) =>
    c.same[index] === null ? undefined : current[c.same[index]],
  )
  const before = stable(recapture(current[0], current))
  const run = attempt(() => reconcile(toJs(c.cur.root, current), toJs(c.next.root, next)))
  if ('error' in run) return [errorReport(seed, run.error)]
  if (run.rejected)
    return reportRejection(seed, expected, stable(recapture(current[0], current)) !== before)
  if (!expected.ok)
    return [{ detail: 'reference rejects; runtime succeeded', kind: 'rejection', seed }]
  const reports: Report[] = []
  compareCaptured(seed, recapture(run.result, current), expected, reports)
  reportGetters(seed, counters, current, expected, reports)
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

/** Builds one object the recipe creates, from drafts and earlier created objects. */
function construct(object: GraphNode, resolve: Resolve): object {
  const o = byKind(shells, object)
  byKind(fillers, object, o, resolve)
  return o
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
  request: (c) => ({ cur: c.cur, next: c.next, op: 'reconcile', same: c.same }),
  show: (c) => `cur  ${stable(c.cur)}\nnext ${stable(c.next)}\nsame ${JSON.stringify(c.same)}`,
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

const GATE_OPTIONS: Options = {
  accessors: true,
  attributes: true,
  nodes: 6,
  reorder: true,
  same: true,
}

/** The seeded batch `check-lean.ts` runs. Until the deterministic engine replaces the current
 * one, `reconcile` differences of the known classes are allowed: `attributes` (the attributes of a
 * moved key), `retention` and `rejection` (where the current engine's plan search keeps an object
 * the deterministic reference does not, or the reverse); getter counts are a report. Every other
 * difference, and any difference of `produce` or `snapshot`, fails. */
export async function checkSpecGate(oracle: Oracle): Promise<void> {
  const allowed = new Set<Report['kind']>(['attributes', 'getters', 'rejection', 'retention'])
  const reconciled = await checkSpec(reconcileCheck, oracle, seeds(1500), GATE_OPTIONS)
  const failing = reconciled.reports.filter((r) => !allowed.has(r.kind))
  assert.deepEqual(
    failing,
    [],
    `Spec reconcile: ${failing.length} differences outside the known classes`,
  )
  const produced = await checkSpec(produceCheck, oracle, seeds(1500), GATE_OPTIONS)
  assert.deepEqual(produced.reports, [], `Spec produce: ${produced.reports.length} differences`)
  const copied = await checkSpec(snapshotCheck, oracle, seeds(500), GATE_OPTIONS)
  assert.deepEqual(copied.reports, [], `Spec snapshot: ${copied.reports.length} differences`)
  console.log(
    `Spec bridge: reconcile ${reconciled.cases} cases (${summary(reconciled.reports)}); produce ${produced.cases} cases (${summary(produced.reports)}); snapshot ${copied.cases} cases (${summary(copied.reports)})`,
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
      dump: { type: 'string' },
      from: { default: '1', type: 'string' },
      nodes: { default: '6', type: 'string' },
      op: { default: 'reconcile', type: 'string' },
      reorder: { default: true, type: 'boolean' },
      same: { default: true, type: 'boolean' },
      seeds: { default: '200', type: 'string' },
      strict: { default: false, type: 'boolean' },
    },
  })
  const { startOracle } = await import('./lean-oracle')
  const oracle = await startOracle()
  try {
    const options: Options = {
      accessors: values.accessors,
      attributes: values.attributes,
      nodes: Number(values.nodes),
      reorder: values.reorder,
      same: values.same,
    }
    assert.ok(values.op in checks, `unknown operation ${values.op}`)
    const check = checks[values.op as keyof typeof checks] as Check<unknown>
    if (values.dump === undefined)
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
