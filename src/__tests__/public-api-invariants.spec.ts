import { assert, describe, it } from 'vitest'
import {
  deserialize,
  isReconcileError,
  produce,
  reconcile,
  requiredMaxBytes,
  serialize,
  snapshot,
} from '../index'
import { genCase, type Case, type Graph } from '../../scripts/spec-generator'
import { materialize, type Counters } from '../../scripts/spec-realize'

// The documented contracts, checked on seeded random graphs far larger than the Spec bridge's
// and without a reference: each check follows from a README sentence and needs no oracle.

type Kind = 'array' | 'date' | 'map' | 'object' | 'set'
const KINDS: ReadonlyArray<[(x: object) => boolean, Kind]> = [
  [Array.isArray, 'array'],
  [(x) => x instanceof Map, 'map'],
  [(x) => x instanceof Set, 'set'],
  [(x) => x instanceof Date, 'date'],
]
const kindOf = (x: object): Kind => KINDS.find(([test]) => test(x))?.[1] ?? 'object'
const isObject = (value: unknown): value is object => typeof value === 'object' && value !== null

type Edges = Map<string, unknown>
/** The children of a value by edge label: a key, an index, `k` or `v` plus the entry index of a
 * `Map`, `m` plus the member index of a `Set`. */
const EDGES: Record<Kind, (value: object) => Edges> = {
  array: (value) => {
    const edges: Edges = new Map()
    const array = value as unknown[]
    for (let index = 0; index < array.length; index += 1)
      if (Object.hasOwn(array, index)) edges.set(String(index), array[index])
    return edges
  },
  date: () => new Map(),
  map: (value) => {
    const edges: Edges = new Map()
    let index = 0
    for (const [k, v] of value as Map<unknown, unknown>) {
      edges.set(`k${index}`, k)
      edges.set(`v${index}`, v)
      index += 1
    }
    return edges
  },
  object: (value) => new Map(Object.keys(value).map((key) => [key, Reflect.get(value, key)])),
  set: (value) => new Map([...(value as Set<unknown>)].map((m, index) => [`m${index}`, m])),
}
const edgesOf = (value: object): Edges => EDGES[kindOf(value)](value)

type Structure = Map<object, Edges>
/** The edges of every object reachable from `root`. */
function structure(root: unknown): Structure {
  const out: Structure = new Map()
  const visit = (value: unknown): void => {
    if (!isObject(value) || out.has(value)) return
    const edges = edgesOf(value)
    out.set(value, edges)
    for (const child of edges.values()) visit(child)
  }
  visit(root)
  return out
}

/** The value at `path` in a recorded structure. */
function at(recorded: Structure, root: object, path: string): unknown {
  let value: unknown = root
  for (const label of path.split('/').slice(1)) {
    if (!isObject(value)) return undefined
    value = recorded.get(value)?.get(label)
  }
  return value
}

/** The edges to walk from `value`: none for a held object, one the walk must not enter. */
const children = (recorded: Structure, held: ReadonlySet<object>, value: object): Edges =>
  held.has(value) ? new Map<string, unknown>() : recorded.get(value)!

/** The path of the first visit of each object reachable from `root`, depth first. */
function positions(root: unknown, held: ReadonlySet<object>): Map<object, string> {
  const recorded = structure(root)
  const out = new Map<object, string>()
  const visit = (value: unknown, path: string): void => {
    if (!isObject(value) || out.has(value)) return
    out.set(value, path)
    for (const [label, child] of children(recorded, held, value)) visit(child, `${path}/${label}`)
  }
  visit(root, '')
  return out
}

function record(out: Map<object, string[]>, value: object, path: string): void {
  const paths = out.get(value)
  if (paths === undefined) out.set(value, [path])
  else paths.push(path)
}

/** Every simple path at which each object is reachable from `root`; a held object ends its
 * paths. The 120-node graphs have at most some hundred thousand paths. */
function placements(root: unknown, held: ReadonlySet<object>): Map<object, string[]> {
  const recorded = structure(root)
  const out = new Map<object, string[]>()
  const stack = new Set<object>()
  const visit = (value: unknown, path: string): void => {
    if (!isObject(value) || stack.has(value)) return
    record(out, value, path)
    stack.add(value)
    for (const [label, child] of children(recorded, held, value)) visit(child, `${path}/${label}`)
    stack.delete(value)
  }
  visit(root, '')
  return out
}

/** Whether two walks found the same objects at the same first paths. */
function samePositions(left: Map<object, string>, right: Map<object, string>): boolean {
  if (left.size !== right.size) return false
  for (const [object, path] of left) if (right.get(object) !== path) return false
  return true
}

type Visit = (l: unknown, r: unknown) => boolean
const sameKeys = (l: object, r: object): boolean => {
  const lk = Reflect.ownKeys(l)
  const rk = Reflect.ownKeys(r)
  return lk.length === rk.length && lk.every((k, index) => k === rk[index])
}
/** Whether two objects of one kind have the same contents, comparing values with `visit`. */
const CONTENTS: Record<Kind, (l: object, r: object, visit: Visit) => boolean> = {
  array: (l, r, visit) =>
    (l as unknown[]).length === (r as unknown[]).length && CONTENTS.object(l, r, visit),
  date: (l, r) => (l as Date).getTime() === (r as Date).getTime(),
  map: (l, r, visit) => {
    const le = [...(l as Map<unknown, unknown>)]
    const re = [...(r as Map<unknown, unknown>)]
    return (
      le.length === re.length &&
      le.every(([k, v], index) => visit(k, re[index][0]) && visit(v, re[index][1]))
    )
  },
  object: (l, r, visit) =>
    sameKeys(l, r) && Reflect.ownKeys(l).every((k) => visit(Reflect.get(l, k), Reflect.get(r, k))),
  set: (l, r, visit) => {
    const le = [...(l as Set<unknown>)]
    const re = [...(r as Set<unknown>)]
    return le.length === re.length && le.every((m, index) => visit(m, re[index]))
  },
}

/** Whether two graphs have the same shape: kinds, own keys in order, holes, entry order, values,
 * sharing and cycles, and prototypes except on the objects in `kept`, which keep their own. */
function isomorphic(left: unknown, right: unknown, kept: ReadonlySet<object> = new Set()): boolean {
  const images = new Map<object, object>()
  const owners = new Set<object>()
  const sameKind = (l: object, r: object): boolean =>
    kindOf(l) === kindOf(r) &&
    (kept.has(l) || Object.getPrototypeOf(l) === Object.getPrototypeOf(r))
  const enter = (l: object, r: object): boolean => {
    if (owners.has(r) || !sameKind(l, r)) return false
    images.set(l, r)
    owners.add(r)
    return CONTENTS[kindOf(l)](l, r, visit)
  }
  const visit: Visit = (l, r) => {
    if (!isObject(l) || !isObject(r)) return Object.is(l, r)
    return images.has(l) ? images.get(l) === r : enter(l, r)
  }
  return visit(left, right)
}

/** The attribute letters of an own property: w, e, c for data and g, e, c for an accessor. */
function attributesOf(o: object, key: string): string {
  const d = Object.getOwnPropertyDescriptor(o, key)!
  const rest = `${d.enumerable === true ? 'e' : ''}${d.configurable === true ? 'c' : ''}`
  return 'value' in d ? `${d.writable === true ? 'w' : ''}${rest}` : `g${rest}`
}

type Attributes = Map<object, Map<string, string>>
const allAttributes = (objects: readonly object[]): Attributes =>
  new Map(
    objects.map((o) => [
      o,
      new Map(Object.getOwnPropertyNames(o).map((key) => [key, attributesOf(o, key)])),
    ]),
  )

const OPTIONS = { accessors: true, attributes: true, nodes: 120, reorder: true, same: true }
const SEEDS = 300

interface Realized {
  counters: Counters
  current: object[]
  held: Set<object>
  next: object[]
}

function realize(c: Case): Realized {
  const counters: Counters = new Map()
  const current = materialize(c.cur, counters)
  const next = materialize(c.next, new Map(), (index) =>
    c.same[index] === null ? undefined : current[c.same[index]],
  )
  const held = new Set(c.same.flatMap((index) => (index === null ? [] : [current[index]])))
  return { counters, current, held, next }
}

/** Runs `operation`; a `PublicationRejected` outcome returns undefined. */
function unlessRejected(operation: () => unknown): unknown {
  try {
    return operation()
  } catch (error) {
    if (isReconcileError(error) && error.cause.type === 'PublicationRejected') return undefined
    throw error
  }
}

/** Asserts that `operation` throws a `ReconcileError` of `type`. */
function throwsType(operation: () => unknown, type: string, message: string): void {
  try {
    operation()
  } catch (error) {
    assert.ok(isReconcileError(error) && error.cause.type === type, `${message}: ${String(error)}`)
    return
  }
  assert.fail(`${message}: nothing was thrown`)
}

function setterCalls(counters: Counters): number {
  let calls = 0
  for (const byKey of counters.values()) for (const count of byKey.values()) calls += count.set
  return calls
}

function resetSetters(counters: Counters): void {
  for (const byKey of counters.values()) for (const count of byKey.values()) count.set = 0
}

const uses = (graph: Graph, feature: string): boolean =>
  JSON.stringify(graph.nodes).includes(`"${feature}"`)

/** The graph with every function and class prototype, which `serialize` rejects, replaced. */
const serializable = (graph: Graph): Graph =>
  JSON.parse(
    JSON.stringify(graph, (_, value: unknown) =>
      isObject(value) && 'atom' in value
        ? `atom${String(value.atom)}`
        : isObject(value) && 'cls' in value
          ? 'object'
          : value,
    ),
  ) as Graph

/** A kept object keeps the attributes of its existing properties; an added property is writable
 * and configurable and takes the enumerability of the property in `next`. */
function checkAttributes(
  seed: number,
  object: object,
  path: string,
  was: Map<string, string>,
  image: object,
): void {
  for (const key of Object.getOwnPropertyNames(object)) {
    const now = attributesOf(object, key)
    const kept = was.get(key)
    if (kept !== undefined) assert.equal(now, kept, `seed ${seed}: ${path}/${key} kept`)
    else {
      const enumerable = Object.getOwnPropertyDescriptor(image, key)?.enumerable === true
      assert.equal(now, `w${enumerable ? 'e' : ''}c`, `seed ${seed}: ${path}/${key} added`)
    }
  }
}

interface Reconciled {
  readonly expected: object
  readonly result: object
}

/** Reconciles a realized case; undefined when the call is rejected. */
function reconcileCase(r: Realized): Reconciled | undefined {
  // `next` is read completely before `current` changes: the result has the shape `next` has now.
  const expected = snapshot(r.next[0]) as object
  const result = unlessRejected(() => reconcile(r.current[0], r.next[0]))
  return result === undefined ? undefined : { expected, result: result as object }
}

/** Every current object in the result is kept at a position current held it, with its
 * attributes; `next` can share it into other positions, which the shape check covers. */
function checkKept(
  seed: number,
  r: Realized,
  before: Map<object, string[]>,
  attributes: Attributes,
  done: Reconciled,
): void {
  const currentSet = new Set(r.current)
  const images = structure(done.expected)
  for (const [object, paths] of placements(done.result, r.held)) {
    if (!currentSet.has(object) || r.held.has(object)) continue
    const own = before.get(object) ?? []
    const path = paths.find((candidate) => own.includes(candidate))
    assert.ok(path !== undefined, `seed ${seed}: ${paths[0]} holds an object kept elsewhere`)
    const image = at(images, done.expected, path) as object
    checkAttributes(seed, object, path, attributes.get(object)!, image)
  }
}

describe('reconcile on large random graphs', () => {
  it('reaches the shape of next, keeps objects at their own positions and keeps attributes', () => {
    let cases = 0
    for (let seed = 1; seed <= SEEDS; seed += 1) {
      const r = realize(genCase(seed, OPTIONS))
      const before = placements(r.current[0], r.held)
      const attributes = allAttributes(r.current)
      const done = reconcileCase(r)
      if (done === undefined) continue
      cases += 1
      assert.strictEqual(done.result, r.current[0], `seed ${seed}: reconcile returns current`)
      assert.ok(
        isomorphic(done.result, done.expected, new Set(r.current)),
        `seed ${seed}: the result has next's shape`,
      )
      checkKept(seed, r, before, attributes, done)
    }
    assert.ok(cases >= SEEDS / 2, `${cases} cases succeeded`)
  })

  it('writes nothing for a next equal to current', () => {
    let cases = 0
    for (let seed = 1; seed <= SEEDS; seed += 1) {
      const r = realize(genCase(seed, OPTIONS))
      const done = reconcileCase(r)
      if (done === undefined) continue
      cases += 1
      const copy = snapshot(done.result)
      const before = positions(done.result, new Set())
      resetSetters(r.counters)
      assert.strictEqual(reconcile(done.result, copy), done.result)
      assert.equal(setterCalls(r.counters), 0, `seed ${seed}: an equal next runs no setter`)
      assert.ok(
        samePositions(positions(done.result, new Set()), before),
        `seed ${seed}: identities`,
      )
      assert.ok(isomorphic(done.result, copy), `seed ${seed}: an equal next changes nothing`)
    }
    assert.ok(cases >= SEEDS / 2, `${cases} cases succeeded`)
  })
})

/** Every property that `deserialize` restores is an ordinary data property. */
function checkOrdinary(seed: number, object: object): void {
  for (const key of Object.getOwnPropertyNames(object))
    if (!Array.isArray(object) || key !== 'length')
      assert.equal(attributesOf(object, key), 'wec', `seed ${seed}: ${key} is ordinary`)
}

function checkRestored(seed: number, copy: unknown): void {
  for (const object of positions(copy, new Set()).keys()) {
    assert.ok(Object.isExtensible(object), `seed ${seed}: every restored object is mutable`)
    if (kindOf(object) === 'object' || kindOf(object) === 'array') checkOrdinary(seed, object)
  }
}

describe('produce, snapshot and serialize on large random graphs', () => {
  const PLAIN = { nodes: 120, reorder: true }

  it('produce returns current for a recipe that changes nothing', () => {
    for (let seed = 1; seed <= SEEDS; seed += 1) {
      const c = genCase(seed, { ...PLAIN, accessors: true, attributes: true })
      const [current] = materialize(c.cur, new Map())
      const before = positions(current, new Set())
      assert.strictEqual(
        produce(current, (draft) => draft),
        current,
        `seed ${seed}: an unchanged draft`,
      )
      assert.strictEqual(
        produce(current, (draft) => {
          positions(draft, new Set())
          return draft
        }),
        current,
        `seed ${seed}: a draft read everywhere`,
      )
      assert.ok(samePositions(positions(current, new Set()), before), `seed ${seed}: unchanged`)
    }
  })

  it('snapshot is a detached copy with the same shape', () => {
    for (let seed = 1; seed <= SEEDS; seed += 1) {
      const c = genCase(seed, { ...PLAIN, accessors: true, attributes: true })
      const [current] = materialize(c.cur, new Map())
      const copy = snapshot(current)
      assert.ok(isomorphic(current, copy), `seed ${seed}: the copy has current's shape`)
      const sources = new Set(positions(current, new Set()).keys())
      for (const object of positions(copy, new Set()).keys())
        assert.ok(!sources.has(object), `seed ${seed}: the copy shares no object`)
    }
  })

  it('serialize round-trips supported graphs and rejects the others', () => {
    for (let seed = 1; seed <= SEEDS; seed += 1) {
      const c = genCase(seed, PLAIN)
      if (uses(c.cur, 'atom') || uses(c.cur, 'cls'))
        throwsType(
          () => serialize(materialize(c.cur, new Map())[0]),
          'SerializeValueUnsupported',
          `seed ${seed}: a function or class instance is rejected`,
        )
      const [current] = materialize(serializable(c.cur), new Map())
      const text = JSON.stringify(serialize(current))
      const required = requiredMaxBytes(JSON.parse(text), { maxBytes: Infinity })
      const copy = deserialize(JSON.parse(text), { maxBytes: required })
      assert.ok(isomorphic(current, copy), `seed ${seed}: the round trip keeps the shape`)
      throwsType(
        () => deserialize(JSON.parse(text), { maxBytes: required - 1 }),
        'DeserializeLimitExceeded',
        `seed ${seed}: one byte less than required is rejected`,
      )
      checkRestored(seed, copy)
    }
  })
})
