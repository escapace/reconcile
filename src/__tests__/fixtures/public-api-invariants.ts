// The documented contracts of every function, checked on seeded random graphs without a
// reference: each check follows from a README sentence and needs no oracle. The spec runs them in
// process; `invariants-hardened.ts` runs a sample in a locked-down child process.
import {
  deserialize,
  isReconcileError,
  produce,
  reconcile,
  requiredMaxBytes,
  serialize,
  snapshot,
} from '../../index'
import { genCase, Rng, type Case, type Graph, type Options } from '../../../scripts/spec-generator'
import { materialize, type Counters } from '../../../scripts/spec-realize'

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
/** The children of a value by edge label: an own string key, an index, `k` or `v` plus the entry
 * index of a `Map`, `m` plus the member index of a `Set`. */
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
  object: (value) =>
    new Map(Object.getOwnPropertyNames(value).map((key) => [key, Reflect.get(value, key)])),
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

/** Every path at which each object is reachable from `root` without passing through itself
 * twice; a held object ends its paths. The 120-node graphs have at most some hundred thousand
 * paths. */
function placements(root: unknown, held: ReadonlySet<object>): Map<object, string[]> {
  const recorded = structure(root)
  const out = new Map<object, string[]>()
  const stack = new Set<object>()
  const visit = (value: unknown, path: string): void => {
    if (!isObject(value)) return
    record(out, value, path)
    if (stack.has(value)) return
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

/** The failure of `operation` not throwing a `ReconcileError` of `type`, if any. */
function throwsType(operation: () => unknown, type: string, message: string): string[] {
  try {
    operation()
  } catch (error) {
    return isReconcileError(error) && error.cause.type === type
      ? []
      : [`${message}: ${String(error)}`]
  }
  return [`${message}: nothing was thrown`]
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
function attributeFailures(
  object: object,
  path: string,
  was: Map<string, string>,
  image: object,
): string[] {
  const failures: string[] = []
  for (const key of Object.getOwnPropertyNames(object)) {
    const now = attributesOf(object, key)
    const kept = was.get(key)
    if (kept !== undefined) {
      if (now !== kept) failures.push(`${path}/${key} had ${kept}, has ${now}`)
    } else {
      const enumerable = Object.getOwnPropertyDescriptor(image, key)?.enumerable === true
      const wanted = `w${enumerable ? 'e' : ''}c`
      if (now !== wanted) failures.push(`${path}/${key} added as ${now}, not ${wanted}`)
    }
  }
  return failures
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
 * attributes; `next` can share it into other positions, which the shape check covers. The own
 * paths are resolved in the result, since a cycle can lead to one through the object itself. */
function keptFailures(
  r: Realized,
  before: Map<object, string[]>,
  attributes: Attributes,
  done: Reconciled,
): string[] {
  const currentSet = new Set(r.current)
  const images = structure(done.expected)
  const after = structure(done.result)
  const failures: string[] = []
  for (const [object, first] of positions(done.result, r.held)) {
    if (!currentSet.has(object) || r.held.has(object)) continue
    const own = before.get(object) ?? []
    const path = own.find((candidate) => at(after, done.result, candidate) === object)
    if (path === undefined) failures.push(`${first} holds an object kept elsewhere`)
    else {
      const image = at(images, done.expected, path) as object
      failures.push(...attributeFailures(object, path, attributes.get(object)!, image))
    }
  }
  return failures
}

/** `reconcile` reaches the shape of `next`, returns `current` and keeps objects at their own
 * positions with their attributes; undefined when the call is rejected. */
export function reconcileInvariants(seed: number, options: Options): string[] | undefined {
  const r = realize(genCase(seed, options))
  const before = placements(r.current[0], r.held)
  const attributes = allAttributes(r.current)
  const done = reconcileCase(r)
  if (done === undefined) return undefined
  const failures: string[] = []
  if (done.result !== r.current[0]) failures.push('reconcile did not return current')
  if (!isomorphic(done.result, done.expected, new Set(r.current)))
    failures.push("the result does not have next's shape")
  return [...failures, ...keptFailures(r, before, attributes, done)]
}

/** A `next` equal to `current` runs no setter and changes no identity or content. */
export function writeFreeInvariants(seed: number, options: Options): string[] | undefined {
  const r = realize(genCase(seed, options))
  const done = reconcileCase(r)
  if (done === undefined) return undefined
  const copy = snapshot(done.result)
  const before = positions(done.result, new Set())
  resetSetters(r.counters)
  const failures: string[] = []
  if (reconcile(done.result, copy) !== done.result)
    failures.push('reconcile did not return current')
  const sets = setterCalls(r.counters)
  if (sets !== 0) failures.push(`an equal next ran ${sets} setters`)
  if (!samePositions(positions(done.result, new Set()), before))
    failures.push('an equal next changed an identity')
  if (!isomorphic(done.result, copy)) failures.push('an equal next changed the contents')
  return failures
}

/** `produce` returns `current` for a recipe that changes nothing, read or unread. */
export function produceInvariants(seed: number, options: Options): string[] {
  const [current] = materialize(genCase(seed, options).cur, new Map())
  const before = positions(current, new Set())
  const failures: string[] = []
  if (produce(current, (draft) => draft) !== current) failures.push('an unchanged draft is new')
  const read = produce(current, (draft) => {
    positions(draft, new Set())
    return draft
  })
  if (read !== current) failures.push('a draft read everywhere is new')
  if (!samePositions(positions(current, new Set()), before)) failures.push('current changed')
  return failures
}

/** `snapshot` is a detached copy with the same shape. */
export function snapshotInvariants(seed: number, options: Options): string[] {
  const [current] = materialize(genCase(seed, options).cur, new Map())
  const copy = snapshot(current)
  const failures: string[] = []
  if (!isomorphic(current, copy)) failures.push("the copy does not have current's shape")
  const sources = new Set(positions(current, new Set()).keys())
  for (const object of positions(copy, new Set()).keys())
    if (sources.has(object)) failures.push('the copy shares an object with current')
  return failures
}

/** Every property that `deserialize` restores is an ordinary data property. */
function ordinaryFailures(object: object): string[] {
  const failures: string[] = []
  for (const key of Object.getOwnPropertyNames(object))
    if ((!Array.isArray(object) || key !== 'length') && attributesOf(object, key) !== 'wec')
      failures.push(`${key} restored as ${attributesOf(object, key)}`)
  return failures
}

function restoredFailures(copy: unknown): string[] {
  const failures: string[] = []
  for (const object of positions(copy, new Set()).keys()) {
    if (!Object.isExtensible(object)) failures.push('a restored object is not extensible')
    if (kindOf(object) === 'object' || kindOf(object) === 'array')
      failures.push(...ordinaryFailures(object))
  }
  return failures
}

/** `serialize` rejects functions and class instances, and otherwise round-trips through
 * `deserialize` at exactly the `requiredMaxBytes` boundary into ordinary objects. */
export function serializeInvariants(seed: number, options: Options): string[] {
  const c = genCase(seed, options)
  const failures: string[] = []
  if (uses(c.cur, 'atom') || uses(c.cur, 'cls'))
    failures.push(
      ...throwsType(
        () => serialize(materialize(c.cur, new Map())[0]),
        'SerializeValueUnsupported',
        'a function or class instance',
      ),
    )
  const [current] = materialize(serializable(c.cur), new Map())
  const text = JSON.stringify(serialize(current))
  const required = requiredMaxBytes(JSON.parse(text), { maxBytes: Infinity })
  const copy = deserialize(JSON.parse(text), { maxBytes: required })
  if (!isomorphic(current, copy)) failures.push('the round trip changed the shape')
  failures.push(
    ...throwsType(
      () => deserialize(JSON.parse(text), { maxBytes: required - 1 }),
      'DeserializeLimitExceeded',
      'one byte less than required',
    ),
  )
  return [...failures, ...restoredFailures(copy)]
}

/* ------------------------------------------------------------------- adversarial effects */

const KEYS = ['a', 'b', 'c', 'd', 'e', 'f']
/** A change to another object of `current`, as a setter or getter with a side effect makes. */
const EFFECTS: Record<Kind, (target: object, rng: Rng) => void> = {
  array: (target) => {
    const array = target as unknown[]
    if (Object.isExtensible(array)) array.push(1)
    else array.length = 0
  },
  date: (target, rng) => (target as Date).setTime(rng.int(1000)),
  map: (target, rng) => (target as Map<unknown, unknown>).set(rng.int(3), rng.int(9)),
  object: (target, rng) => {
    const key = rng.pick(KEYS)
    if (rng.chance(0.5)) Reflect.set(target, key, rng.int(9))
    else Reflect.deleteProperty(target, key)
  },
  set: (target, rng) => (target as Set<unknown>).add(rng.int(3)),
}

/** A change to a random target, made by an accessor; a frozen target refuses it silently. */
const effectOn = (targets: readonly object[], rng: Rng) => (): void => {
  const target = rng.pick(targets)
  try {
    EFFECTS[kindOf(target)](target, rng)
  } catch {
    // The target refused the change; the effect then changes nothing.
  }
}

/** The configurable own accessors of an object, which can be redefined. */
const configurableAccessors = (object: object): Array<[string, PropertyDescriptor]> =>
  Object.getOwnPropertyNames(object)
    .map((key): [string, PropertyDescriptor] => [
      key,
      Object.getOwnPropertyDescriptor(object, key)!,
    ])
    .filter(([, d]) => !('value' in d) && d.configurable === true)

function armAccessor(
  object: object,
  key: string,
  d: PropertyDescriptor,
  effect: () => void,
  effects: 'getters' | 'setters',
): void {
  // The accessor functions are wrapped, not called, so their `this` stays the receiver's.
  // eslint-disable-next-line typescript/unbound-method
  const { get, set } = d
  Object.defineProperty(object, key, {
    ...d,
    get: effects === 'getters' && get !== undefined ? withEffect(get, effect) : get,
    set: effects === 'setters' && set !== undefined ? withEffect(set, effect) : set,
  })
}

/** Redefines each configurable own accessor of the current objects so that its setter, or its
 * getter, also changes another current object that `next` does not reach. */
function armEffects(r: Realized, rng: Rng, effects: 'getters' | 'setters'): number {
  const reachable = new Set(positions(r.next[0], new Set()).keys())
  const targets = r.current.filter((o) => !r.held.has(o) && !reachable.has(o))
  if (targets.length === 0) return 0
  let armed = 0
  for (const object of r.current) {
    if (r.held.has(object) || kindOf(object) !== 'object') continue
    for (const [key, d] of configurableAccessors(object)) {
      armed += 1
      armAccessor(object, key, d, effectOn(targets, rng), effects)
    }
  }
  return armed
}

const withEffect = (accessor: (...parameters: unknown[]) => unknown, effect: () => void) =>
  function (this: unknown, ...parameters: unknown[]): unknown {
    effect()
    return Reflect.apply(accessor, this, parameters)
  }

export interface AdversarialOutcome {
  readonly armed: number
  readonly failures: string[]
  readonly rejected: boolean
}

/** With accessors that change other objects during the call, `reconcile` still either rejects
 * the call or reaches the shape `next` had when the call began, replacing the objects whose
 * writes were disturbed, and throws nothing else. */
export function adversarialInvariants(
  seed: number,
  options: Options,
  effects: 'getters' | 'setters',
): AdversarialOutcome {
  const r = realize(genCase(seed, options))
  const armed = armEffects(r, new Rng(seed * 7919), effects)
  const expected = snapshot(r.next[0]) as object
  const result = unlessRejected(() => reconcile(r.current[0], r.next[0]))
  if (result === undefined) return { armed, failures: [], rejected: true }
  const failures: string[] = []
  if (result !== r.current[0]) failures.push('reconcile did not return current')
  if (!isomorphic(result, expected, new Set(r.current)))
    failures.push("the result does not have next's shape")
  return { armed, failures, rejected: false }
}
