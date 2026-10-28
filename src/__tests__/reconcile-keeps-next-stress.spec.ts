// Stress for the rule that `reconcile` never changes `next` (`Spec.KeepsNext`): seeded `current`
// graphs of every kind, and `next` values built from them with the immutable idioms applications
// use, which share the objects of `current` in place or moved, and with `produce`. Every call either
// reaches `next` or throws `PublicationWouldChangeNext`; `next` keeps its identities and contents
// both ways, a rejection leaves `current` as it was, since no graph here blocks a write and makes
// `reconcile` try again, and a case built again has the same outcome.
import { assert, describe, it } from 'vitest'
import { isReconcileError, produce, reconcile } from '../index'
import { assertSameState, graphState, type GraphState } from './fixtures/graph-state'
import { Random } from './fixtures/native-differential'

type Bag = Record<PropertyKey, unknown>

const isObject = (value: unknown): value is object =>
  (typeof value === 'object' && value !== null) || typeof value === 'function'

/** A class instance: own fields, and a prototype getter `reconcile` never writes. */
class Item {
  label: string
  n: number
  constructor(label: string, n: number) {
    this.label = label
    this.n = n
  }
  get double(): number {
    return this.n * 2
  }
}

/* ------------------------------------------------------------------------------- current */

/** Builds `current` graphs and remembers every object it made, for `next` to move. */
class Builder {
  private count = 0
  readonly pool: object[] = []
  constructor(
    readonly random: Random,
    readonly root: Bag,
  ) {}

  /** A number no other value of the graph holds. */
  fresh(): number {
    this.count += 1
    return this.count
  }

  keep<T extends object>(value: T): T {
    this.pool.push(value)
    return value
  }

  /** A primitive, an object built here, or an object built earlier, shared. */
  value(depth: number, parent: object): unknown {
    const random = this.random
    if (depth > 3 || random.chance(0.3))
      return random.chance(0.5) ? this.fresh() : `s${this.fresh()}`
    if (this.pool.length > 0 && random.chance(0.12)) return random.pick(this.pool)
    if (random.chance(0.06)) return random.chance(0.5) ? this.root : parent
    return this.object(depth + 1)
  }

  object(depth: number): object {
    const make = this.random.pick(MAKERS)
    return make(this, depth)
  }

  /** Fills `target` with up to four keys, in a random order. */
  fill(target: Bag, depth: number): Bag {
    const keys = this.random.shuffle(['a', 'b', 'c', 'd', 'e']).slice(0, 1 + this.random.int(4))
    for (const key of keys) target[key] = this.value(depth, target)
    return target
  }
}

/** An object with accessors that store what they are given, beside data properties. */
function accessorObject(builder: Builder, depth: number): object {
  const target = builder.fill({}, depth)
  let stored: unknown = builder.fresh()
  Object.defineProperty(target, 'acc', {
    configurable: true,
    enumerable: true,
    get: () => stored,
    set: (value: unknown) => {
      stored = value
    },
  })
  const constant = builder.fresh()
  Object.defineProperty(target, 'fixed', {
    configurable: true,
    enumerable: true,
    get: () => constant,
  })
  return target
}

/** A buffer, views over it and another buffer, and a `DataView` range. */
function binary(builder: Builder): object {
  const random = builder.random
  const bytes = (length: number) => Uint8Array.from({ length }, () => random.int(256))
  const buffer = bytes(4).buffer
  const other = bytes(4).buffer
  return {
    buffer,
    data: new DataView(buffer, 1, 2),
    other,
    shorts: new Int16Array(other),
    view: new Uint8Array(buffer),
  }
}

/** A URL, sometimes beside its `searchParams`, and another URL. */
function urls(builder: Builder): object {
  const url = new URL(`https://h${builder.fresh()}.test/p?x=${builder.fresh()}`)
  const other = new URL(`https://o${builder.fresh()}.test/?y=1`)
  return builder.random.chance(0.5) ? { other, url } : { other, params: url.searchParams, url }
}

const MAKERS: ReadonlyArray<(builder: Builder, depth: number) => object> = [
  (builder, depth) => builder.keep(builder.fill({}, depth)),
  (builder, depth) => builder.keep(builder.fill({}, depth)),
  (builder, depth) => {
    const array: unknown[] = []
    const length = builder.random.int(6)
    for (let index = 0; index < length; index += 1)
      if (builder.random.chance(0.8)) array[index] = builder.value(depth, array)
    array.length = length
    return builder.keep(array)
  },
  (builder, depth) => {
    const map = new Map<unknown, unknown>()
    for (let entry = builder.random.int(4); entry > 0; entry -= 1) {
      const key = builder.random.chance(0.5) ? `k${builder.fresh()}` : builder.object(depth + 2)
      map.set(key, builder.value(depth, map))
    }
    return builder.keep(map)
  },
  (builder, depth) => {
    const set = new Set<unknown>()
    for (let member = builder.random.int(4); member > 0; member -= 1)
      set.add(builder.value(depth, set))
    return builder.keep(set)
  },
  (builder) => builder.keep(new Date(builder.fresh() * 1000)),
  (builder) => builder.keep(binary(builder)),
  (builder) => builder.keep(urls(builder)),
  (builder, depth) => {
    const item = new Item(`i${builder.fresh()}`, builder.fresh())
    if (builder.random.chance(0.5)) (item as unknown as Bag).child = builder.value(depth, item)
    return builder.keep(item)
  },
  (builder, depth) => builder.keep(Object.freeze(builder.fill({}, depth))),
  (builder, depth) => builder.keep(Object.seal(builder.fill({}, depth))),
  (builder, depth) => builder.keep(accessorObject(builder, depth)),
]

/** A `current` graph: a plain root of data properties, which can always be updated in place. */
function buildCurrent(random: Random): Builder {
  const builder = new Builder(random, {})
  builder.fill(builder.root, 0)
  return builder
}

/* ---------------------------------------------------------------------------------- next */

/** Builds `next` from `current` with immutable idioms: each object it reaches is kept, or
 * replaced by a copy that an idiom changed, which can hold new objects and objects moved from
 * anywhere in `current`. */
class Editor {
  private readonly seen = new Set<object>()
  constructor(
    readonly random: Random,
    readonly pool: readonly object[],
    readonly fresh: () => number,
  ) {}

  /** A new object, an object of `current` moved here, or a primitive. */
  other(): unknown {
    const random = this.random
    if (this.pool.length > 0 && random.chance(0.5)) return random.pick(this.pool)
    return random.chance(0.5)
      ? { n: this.fresh() }
      : random.chance(0.5)
        ? [this.fresh()]
        : this.fresh()
  }

  /** `value`, or a copy that an idiom of its kind changed; a date takes a new time, and a buffer,
   * view or URL stays. */
  edit(value: unknown, force = false): unknown {
    if (!this.chosen(value, force)) return value
    this.seen.add(value)
    return (IDIOMS[kindOf(value)] as (editor: Editor, value: object) => unknown)(this, value)
  }

  /** Whether to change `value`: an object not met yet, sometimes. */
  private chosen(value: unknown, force: boolean): value is object {
    return isObject(value) && !this.seen.has(value) && (force || !this.random.chance(0.45))
  }

  /** A copy of `array` with some elements edited. */
  mapped(array: readonly unknown[]): unknown[] {
    return array.map((element) => this.edit(element))
  }
}

/** Two distinct keys of `target`, or undefined when it has fewer. */
function twoKeys(editor: Editor, target: Bag): [string, string] | undefined {
  const keys = Object.keys(target)
  if (keys.length < 2) return undefined
  const [first, second] = editor.random.shuffle(keys)
  return [first, second]
}

const OBJECT_IDIOMS: ReadonlyArray<(editor: Editor, target: Bag) => unknown> = [
  // Spread with edited values, a new or moved value, and a key removed.
  (editor, target) => {
    const copy: Bag = { ...target }
    for (const key of Object.keys(copy)) copy[key] = editor.edit(copy[key])
    if (editor.random.chance(0.5)) copy[`n${editor.fresh()}`] = editor.other()
    const keys = Object.keys(copy)
    if (keys.length > 1 && editor.random.chance(0.3)) delete copy[editor.random.pick(keys)]
    return copy
  },
  // Swapped values.
  (editor, target) => {
    const keys = twoKeys(editor, target)
    return keys === undefined
      ? { ...target, z: editor.other() }
      : { ...target, [keys[0]]: target[keys[1]], [keys[1]]: target[keys[0]] }
  },
  // A renamed key.
  (editor, target) => {
    const keys = Object.keys(target)
    if (keys.length === 0) return { r: editor.other() }
    const key = editor.random.pick(keys)
    const { [key]: moved, ...rest } = target
    return { ...rest, [`${key}2`]: moved }
  },
  // Keys in reverse order, values edited.
  (editor, target) =>
    Object.fromEntries(
      Object.entries(target)
        .reverse()
        .map(([key, value]) => [key, editor.edit(value)]),
    ),
  // A value replaced by a new or moved one.
  (editor, target) => {
    const keys = Object.keys(target)
    const key = keys.length === 0 ? 'm' : editor.random.pick(keys)
    return { ...target, [key]: editor.other() }
  },
  // A view moved to another buffer, a URL moved, or the parameters of another URL.
  (editor, target) => {
    if ('view' in target)
      return { ...target, data: target.shorts, view: new Uint8Array(target.other as ArrayBuffer) }
    if ('url' in target)
      return editor.random.chance(0.5)
        ? { ...target, other: target.url, url: target.other }
        : { ...target, params: (target.other as URL).searchParams }
    return { ...target }
  },
]

const ARRAY_IDIOMS: ReadonlyArray<(editor: Editor, array: unknown[]) => unknown> = [
  (_editor, array) => array.slice(1),
  (_editor, array) => array.slice(0, -1),
  (editor, array) => {
    const copy = array.slice()
    copy.splice(editor.random.int(copy.length + 1), editor.random.int(2), editor.other())
    return copy
  },
  (editor, array) => array.filter(() => editor.random.chance(0.6)),
  (editor, array) => {
    const ranks = new Map<unknown, number>()
    for (const element of array) ranks.set(element, editor.random.next())
    return array.slice().sort((left, right) => ranks.get(left)! - ranks.get(right)!)
  },
  (_editor, array) => array.slice().reverse(),
  (editor, array) => {
    const copy = array.slice()
    copy.unshift(editor.other())
    return copy
  },
  (editor, array) => array.concat([editor.other()]),
  (_editor, array) => array.map((element) => element),
  (editor, array) => editor.mapped(array),
]

const MAP_IDIOMS: ReadonlyArray<(editor: Editor, map: Map<unknown, unknown>) => unknown> = [
  (editor, map) => {
    const copy = new Map(map)
    const keys = [...copy.keys()]
    if (keys.length > 0) copy.delete(editor.random.pick(keys))
    return copy
  },
  (editor, map) =>
    new Map(map).set(editor.random.chance(0.5) ? editor.other() : 'new', editor.other()),
  (_editor, map) => new Map([...map].reverse()),
  (editor, map) => {
    const values = editor.random.shuffle([...map.values()])
    return new Map([...map.keys()].map((key, index) => [key, values[index]]))
  },
  (editor, map) => new Map([...map].map(([key, value]) => [key, editor.edit(value)])),
]

const SET_IDIOMS: ReadonlyArray<(editor: Editor, set: Set<unknown>) => unknown> = [
  (editor, set) => {
    const copy = new Set(set)
    const members = [...copy]
    if (members.length > 0) copy.delete(editor.random.pick(members))
    return copy
  },
  (editor, set) => new Set(set).add(editor.other()),
  (_editor, set) => new Set([...set].reverse()),
  (editor, set) => new Set([...set].map((member) => editor.edit(member))),
]

/** The change an editor makes to an object of each kind. */
const IDIOMS: Record<string, (editor: Editor, value: never) => unknown> = {
  array: (editor, value: unknown[]) => editor.random.pick(ARRAY_IDIOMS)(editor, value),
  buffer: (_editor, value: object) => value,
  date: (_editor, value: Date) => new Date(value.getTime() + 1),
  function: (_editor, value: object) => value,
  map: (editor, value: Map<unknown, unknown>) => editor.random.pick(MAP_IDIOMS)(editor, value),
  object: (editor, value: Bag) => editor.random.pick(OBJECT_IDIOMS)(editor, value),
  params: (_editor, value: object) => value,
  set: (editor, value: Set<unknown>) => editor.random.pick(SET_IDIOMS)(editor, value),
  url: (_editor, value: object) => value,
  view: (_editor, value: object) => value,
}

/** A case: `current`, and `next` built from it. */
interface Built {
  readonly current: Bag
  readonly next: unknown
}

/** `next` from `current` by immutable idioms; the root is always a new object. */
function nextByIdioms(seed: number): Built {
  const builder = buildCurrent(new Random(seed))
  const editor = new Editor(new Random(seed * 31 + 7), builder.pool, () => builder.fresh())
  return { current: builder.root, next: editor.edit(builder.root, true) }
}

/* ------------------------------------------------------------------------------- produce */

type DraftStep<T> = (random: Random, draft: T, others: unknown[]) => void

/** Picks a step of `table`, whose first `moves` steps reorder or move what the draft holds, so
 * that most steps move objects the recipe leaves unchanged. */
const stepOf = <T>(random: Random, table: ReadonlyArray<DraftStep<T>>, moves: number) =>
  random.chance(0.6) ? table[random.int(moves)] : random.pick(table)

/** The same operations on a draft: reorders, moves, removals and insertions of objects the
 * recipe leaves unchanged, and changes to a few. */
function recipeStep(random: Random, draft: unknown, others: unknown[]): void {
  if (Array.isArray(draft)) stepOf(random, DRAFT_ARRAY, 3)(random, draft, others)
  else if (draft instanceof Map) stepOf(random, DRAFT_MAP, 2)(random, draft, others)
  else if (draft instanceof Set) stepOf(random, DRAFT_SET, 1)(random, draft, others)
  else stepOf(random, DRAFT_OBJECT, 3)(random, draft as Bag, others)
}

/** Reorders a draft's entries, which `clear` and re-adding do on a `Map` or `Set`. */
function reorder<K, V>(draft: Map<K, V>, entries: ReadonlyArray<[K, V]>): void {
  draft.clear()
  for (const [key, value] of entries) draft.set(key, value)
}

const DRAFT_ARRAY: ReadonlyArray<DraftStep<unknown[]>> = [
  (_random, draft) => void draft.reverse(),
  (random, draft) => {
    const ranks = draft.map(() => random.next())
    const order = draft.map((_, index) => index).sort((left, right) => ranks[left] - ranks[right])
    const values = order.map((index) => draft[index])
    for (let index = 0; index < values.length; index += 1) draft[index] = values[index]
  },
  (_random, draft) => {
    if (draft.length > 1) draft.push(...draft.splice(0, 1))
  },
  (random, draft) => void draft.splice(random.int(draft.length + 1), 1),
  (random, draft, others) => void draft.unshift(random.pick(others)),
  (random, draft, others) => void draft.push(random.pick(others)),
]

const DRAFT_MAP: ReadonlyArray<DraftStep<Map<unknown, unknown>>> = [
  (_random, draft) => reorder(draft, [...draft].reverse()),
  (random, draft) => {
    const values = random.shuffle([...draft.values()])
    reorder(
      draft,
      [...draft.keys()].map((key, index) => [key, values[index]]),
    )
  },
  (random, draft) => {
    const keys = [...draft.keys()]
    if (keys.length > 0) draft.delete(random.pick(keys))
  },
  (random, draft, others) => void draft.set(`k${random.int(1000)}`, random.pick(others)),
]

const DRAFT_SET: ReadonlyArray<DraftStep<Set<unknown>>> = [
  (_random, draft) => {
    const members = [...draft].reverse()
    draft.clear()
    for (const member of members) draft.add(member)
  },
  (random, draft) => {
    const members = [...draft]
    if (members.length > 0) draft.delete(random.pick(members))
  },
  (random, draft, others) => void draft.add(random.pick(others)),
]

/** The keys of a draft's writable and configurable data properties, which a recipe can assign
 * and delete. */
const dataKeys = (draft: Bag): string[] =>
  Object.keys(draft).filter((key) => {
    const descriptor = Object.getOwnPropertyDescriptor(draft, key)!
    return 'value' in descriptor && descriptor.writable === true && descriptor.configurable === true
  })

/** Whether a recipe can assign the properties of `value`: an object other than an array,
 * `Map` or `Set`. */
const isRecord = (value: unknown): value is Bag =>
  isObject(value) && !Array.isArray(value) && !(value instanceof Map) && !(value instanceof Set)

// A draft of a frozen or sealed object reports itself extensible but refuses writes, which
// `Reflect` reports instead of throwing.
const DRAFT_OBJECT: ReadonlyArray<DraftStep<Bag>> = [
  // Two values swapped.
  (random, draft) => {
    const keys = dataKeys(draft)
    if (keys.length < 2) return
    const [first, second] = random.shuffle(keys)
    const held = draft[first]
    if (Reflect.set(draft, first, draft[second])) Reflect.set(draft, second, held)
  },
  // Values swapped with another draft.
  (random, draft, others) => {
    const other = random.pick(others)
    if (!isRecord(other)) return
    const mine = dataKeys(draft)
    const theirs = dataKeys(other)
    if (mine.length === 0 || theirs.length === 0) return
    const key = random.pick(mine)
    const otherKey = random.pick(theirs)
    const held = draft[key]
    if (Reflect.set(draft, key, other[otherKey])) Reflect.set(other, otherKey, held)
  },
  // A renamed key.
  (random, draft) => {
    const keys = dataKeys(draft)
    if (keys.length === 0) return
    const key = random.pick(keys)
    const value = draft[key]
    if (Reflect.deleteProperty(draft, key)) Reflect.set(draft, `${key}2`, value)
  },
  (random, draft, others) => void Reflect.set(draft, `n${random.int(1000)}`, random.pick(others)),
  (random, draft) => {
    const keys = dataKeys(draft)
    if (keys.length > 0) Reflect.deleteProperty(draft, random.pick(keys))
  },
  (random, draft) => void Reflect.set(draft, 'changed', random.int(1000)),
]

/** Whether a recipe step can change `value`: an array, `Map`, `Set` or another object that is not
 * a date, buffer, view or URL. */
const isContainer = (value: unknown): boolean =>
  isObject(value) &&
  !(value instanceof Date) &&
  !(value instanceof ArrayBuffer) &&
  !ArrayBuffer.isView(value) &&
  !(value instanceof URL) &&
  !(value instanceof URLSearchParams)

/** The drafts a recipe can reach from `draft` through plain objects, arrays, maps and sets, in a
 * walk of at most `limit` objects. */
function reachable(draft: unknown, limit: number): unknown[] {
  const found: unknown[] = []
  const seen = new Set<unknown>()
  const wanted = (value: unknown): value is object =>
    isObject(value) && !seen.has(value) && found.length < limit
  const visit = (value: unknown): void => {
    if (!wanted(value)) return
    seen.add(value)
    found.push(value)
    for (const child of childrenOf(value)) visit(child)
  }
  visit(draft)
  return found
}

/** Whether a recipe walks into the keys of `value`: an array or a plain object. */
const walksKeys = (value: object): boolean => Array.isArray(value) || value.constructor === Object

/** The values a recipe walks into from `value`: the values of a `Map`, the members of a `Set` and
 * the values at the keys of an array or a plain object. */
function childrenOf(value: object): unknown[] {
  if (value instanceof Map) return [...value.values()]
  if (value instanceof Set) return [...value]
  return walksKeys(value) ? Object.keys(value).map((key) => (value as Bag)[key]) : []
}

/** `next` as `produce(current, recipe)` with the same operations on drafts; undefined when
 * `produce` rejects the recipe, as when it puts one object into a new `Set` twice. */
function nextByRecipe(seed: number): Built | undefined {
  const builder = buildCurrent(new Random(seed))
  const random = new Random(seed * 17 + 3)
  try {
    const next = produce(builder.root, (draft) => {
      const drafts = reachable(draft, 24)
      const targets = drafts.filter(isContainer)
      const others = [...drafts, { n: random.int(1000) }, random.int(1000)]
      for (let step = 2 + random.int(6); step > 0; step -= 1)
        recipeStep(random, random.pick(targets), others)
      return draft
    })
    return { current: builder.root, next }
  } catch (error) {
    if (isReconcileError(error)) return undefined
    throw error
  }
}

/* ---------------------------------------------------------------------------------- checks */

/** The kinds of objects, by the test that recognizes each, in order; any other object is a plain
 * or class object. */
const KINDS: ReadonlyArray<[kind: string, test: (value: object) => boolean]> = [
  ['array', (value) => Array.isArray(value)],
  ['map', (value) => value instanceof Map],
  ['set', (value) => value instanceof Set],
  ['date', (value) => value instanceof Date],
  ['buffer', (value) => value instanceof ArrayBuffer],
  ['view', (value) => ArrayBuffer.isView(value)],
  ['url', (value) => value instanceof URL],
  ['params', (value) => value instanceof URLSearchParams],
  ['function', (value) => typeof value === 'function'],
]

/** The kind of an object as `reconcile` matches it; objects of one kind compare alike. */
const kindOf = (value: object): string => KINDS.find(([, test]) => test(value))?.[0] ?? 'object'

type Pair = (left: unknown, right: unknown) => void

function compareViews(left: ArrayBufferView, right: ArrayBufferView, pair: Pair): void {
  assert.equal(right.constructor, left.constructor, 'view type')
  assert.equal(right.byteOffset, left.byteOffset, 'view offset')
  assert.equal(right.byteLength, left.byteLength, 'view length')
  pair(left.buffer, right.buffer)
}

/** Compares the contents of two objects of one kind, pairing their children with `pair`. */
const CONTENTS: Record<string, (left: never, right: never, pair: Pair) => void> = {
  view: compareViews,
  buffer: (left: ArrayBuffer, right: ArrayBuffer) =>
    assert.deepEqual([...new Uint8Array(right)], [...new Uint8Array(left)], 'buffer bytes'),
  date: (left: Date, right: Date) => assert.equal(right.getTime(), left.getTime(), 'date'),
  function: () => assert.fail('a function is kept by reference'),
  map: (left: Map<unknown, unknown>, right: Map<unknown, unknown>, pair) => {
    const rightEntries = [...right]
    assert.equal(rightEntries.length, left.size, 'map size')
    ;[...left].forEach(([key, value], index) => {
      pair(key, rightEntries[index][0])
      pair(value, rightEntries[index][1])
    })
  },
  params: (left: URLSearchParams, right: URLSearchParams) =>
    assert.equal(String(right), String(left), 'search parameters'),
  set: (left: Set<unknown>, right: Set<unknown>, pair) => {
    const members = [...right]
    assert.equal(members.length, left.size, 'set size')
    ;[...left].forEach((member, index) => pair(member, members[index]))
  },
  url: (left: URL, right: URL, pair) => {
    assert.equal(right.href, left.href, 'url')
    pair(left.searchParams, right.searchParams)
  },
}

function compareProperties(left: object, right: object, pair: Pair): void {
  const keys = Reflect.ownKeys(left)
  assert.deepEqual(Reflect.ownKeys(right), keys, 'own keys')
  for (const key of keys) pair(Reflect.get(left, key), Reflect.get(right, key))
}

/** Asserts that `actual` has the contents, order and sharing of `expected`: a bijection between
 * their objects that pairs equal primitives and objects of one kind with equal contents.
 * Prototypes are not compared, since an object `reconcile` keeps keeps its own. */
function assertSameGraph(expected: unknown, actual: unknown): void {
  const images = new Map<object, object>()
  const owners = new Set<object>()
  const pending: Array<[object, object]> = []
  const pair: Pair = (left, right) => {
    if (!isObject(left) || typeof left === 'function') return void assert.ok(Object.is(left, right))
    assert.ok(isObject(right), 'an object became a primitive')
    const image = images.get(left)
    if (image !== undefined) return void assert.equal(right, image, 'sharing differs')
    assert.notOk(owners.has(right), 'two objects became one')
    assert.equal(kindOf(right), kindOf(left), 'kind')
    images.set(left, right)
    owners.add(right)
    pending.push([left, right])
  }
  pair(expected, actual)
  for (let at = 0; at < pending.length; at += 1) {
    const [left, right] = pending[at]
    const compare = CONTENTS[kindOf(left)] as ((l: object, r: object, p: Pair) => void) | undefined
    ;(compare ?? compareProperties)(left, right, pair)
  }
}

/** Each object of the graph after the call by where it came from: an object of `current` or of
 * `next` before the call, by index, or a new one; and the contents. A case built again must
 * end with the same text. */
function signature(state: GraphState, current: GraphState, next: GraphState): string {
  const origins = state.objects.map((object) => {
    const fromCurrent = current.objects.indexOf(object)
    return fromCurrent >= 0 ? `c${fromCurrent}` : `n${next.objects.indexOf(object)}`
  })
  return `${origins.join()}\n${state.text}`
}

interface Outcome {
  readonly rejected: boolean
  readonly signature: string
}

/** Runs one case and checks the rule's promises (a) to (c); the outcome serves (d). */
function runCase({ current, next }: Built): Outcome {
  const currentBefore = graphState(current)
  const nextBefore = graphState(next)
  let result: unknown
  let rejected = false
  try {
    result = reconcile(current, next)
  } catch (error) {
    if (!isReconcileError(error) || error.cause.type !== 'PublicationWouldChangeNext') throw error
    rejected = true
  }
  // (b) `next` keeps its identities and contents.
  assertSameState(nextBefore, graphState(next), 'next')
  const after = graphState(current)
  // (c) A rejection leaves `current` as it was; (a) a success reaches `next` as built.
  if (rejected) assertSameState(currentBefore, after, 'current')
  else {
    assert.equal(result, current)
    assertSameGraph(next, current)
  }
  return { rejected, signature: signature(after, currentBefore, nextBefore) }
}

interface Tally {
  cases: number
  rejected: number
}

/** Runs `count` seeded cases twice each, built afresh; (d) the second run must end like the
 * first. A seed whose `next` cannot be built is skipped. */
function stress(count: number, make: (seed: number) => Built | undefined): Tally {
  const tally: Tally = { cases: 0, rejected: 0 }
  for (let seed = 1; seed <= count; seed += 1) {
    try {
      const built = make(seed)
      if (built === undefined) continue
      const first = runCase(built)
      assert.deepEqual(runCase(make(seed)!), first, 'the outcome differs between runs')
      tally.cases += 1
      if (first.rejected) tally.rejected += 1
    } catch (cause) {
      throw new Error(`seed ${seed}`, { cause })
    }
  }
  return tally
}

const SEEDS = 1500

/** Both outcomes occur often enough to matter. */
function assertMixed({ cases, rejected }: Tally): void {
  console.log(`TALLY ${cases} ${rejected}`)
  assert.isAbove(cases, SEEDS * 0.9, 'cases built')
  assert.isAbove(rejected, cases / 20, 'rejections')
  assert.isBelow(rejected, cases - cases / 20, 'rejections')
}

/** An object whose `s` reads 1 and whose setter drops what it is given. */
function dropping(): object {
  const target = {}
  Object.defineProperty(target, 's', {
    configurable: true,
    enumerable: true,
    get: () => 1,
    set: () => undefined,
  })
  return target
}

/** The examples of `Spec.KeepsNext` and a few more, with the outcome each must have: whether the
 * call rejects, and whether a rejection comes after a pass that wrote into `current`. */
const EXAMPLES: ReadonlyArray<[name: string, build: () => Built, outcome: 'reaches' | 'rejects']> =
  [
    [
      'swap',
      () => {
        const current = { a: { v: 1 }, b: { v: 2 } }
        return { current, next: { a: current.b, b: current.a } }
      },
      'rejects',
    ],
    [
      'mapChild',
      () => {
        // `p` comes first, so the node of `child` keeps the object `current` holds at `p`.
        const child = { v: 2 }
        const held = { c: child }
        const current: Bag = { p: { v: 1 } }
        current.m = new Map([[1, held]])
        const next: Bag = { p: child }
        next.m = new Map([[1, held]])
        return { current, next }
      },
      'rejects',
    ],
    [
      'equalCopy',
      () => {
        const current = { a: { v: 1 }, b: { v: 2 } }
        return { current, next: { a: current.b, b: { v: 2 } } }
      },
      'rejects',
    ],
    [
      'inPlace',
      () => {
        const current = { a: { v: 1 } }
        return { current, next: { ...current, n: 1 } }
      },
      'reaches',
    ],
    [
      'rootCycle',
      () => {
        const current: Bag = { a: {} }
        ;(current.a as Bag).up = current
        return { current, next: { ...current, n: 1 } }
      },
      'rejects',
    ],
    [
      'urlSwap',
      () => {
        const current = { a: new URL('https://a.test/?x=1'), b: new URL('https://b.test/?y=2') }
        return { current, next: { a: current.b, b: current.a } }
      },
      'rejects',
    ],
    [
      'sharedInPlace',
      () => {
        const shared = { v: 1 }
        const current = { a: shared, b: shared }
        return { current, next: { ...current, c: shared, n: 1 } }
      },
      'reaches',
    ],
  ]

describe('reconcile never changes next', () => {
  it('has the outcome each example states', () => {
    for (const [name, build, outcome] of EXAMPLES) {
      const first = runCase(build())
      assert.equal(first.rejected, outcome === 'rejects', name)
      assert.deepEqual(runCase(build()), first, name)
    }
  })

  it('rejects after a pass that wrote into current, never into next', () => {
    // `Spec.KeepsNext` example `laterPass`: the first pass keeps the dropping object at the new
    // object's node and writes into current only; the second keeps y, which next holds at c.
    const y = { s: 1 }
    const current: Bag = { a: dropping(), b: y }
    const fresh = { s: 2 }
    const next = { a: fresh, b: fresh, c: y }
    const nextBefore = graphState(next)
    let error: unknown
    try {
      reconcile(current, next)
    } catch (caught) {
      error = caught
    }
    assert.ok(isReconcileError(error))
    assert.deepEqual(error.cause, { type: 'PublicationWouldChangeNext' })
    assertSameState(nextBefore, graphState(next), 'next')
    assert.deepEqual(y, { s: 1 })
  })

  it(`reaches or rejects ${SEEDS} next values built with immutable idioms`, () => {
    assertMixed(stress(SEEDS, nextByIdioms))
  })

  it(`reaches or rejects ${SEEDS} next values that produce builds`, () => {
    assertMixed(stress(SEEDS, nextByRecipe))
  })
})
