// Exhaustive differential check of the `Spec` family on small cases. Each universe lists every
// case within its bound: `reconcile` over graphs of a few nodes and slots, over attributes,
// accessors and class prototype slots, over `Map` and `Set` entries, over array holes and
// integrity levels, over dates and over buffers and views; `produce` over every short recipe on
// small graphs; and `snapshot` over every current graph listed. Each `reconcile` case runs through
// the Spec bridge, plain and through recording proxies, and through the phase bridge.
//
// Standalone: pnpm exec tsx scripts/check/bridges/spec-enumeration.ts [--only NAME] [--count]
// --only NAME runs one universe; --count prints each universe's number of cases without running
// them.
import assert from 'node:assert/strict'
import { parseArgs } from 'node:util'
import type { Oracle } from '../oracle'
import {
  checkCases,
  produceCheck,
  reconcileCheck,
  snapshotCheck,
  type Check,
  type Report,
} from './spec'
import { checkPhaseCases, instrumented, type Library } from './spec-phases'
import {
  byKind,
  draftPaths,
  isHole,
  isReference,
  mapReferences,
  type Case,
  type Classes,
  type Extensibility,
  type ByKind,
  type Graph,
  type GraphNode,
  type NodeOf,
  type Op,
  type Recipe,
  type Slot,
  type Value,
  type ViewConstructor,
} from '../fixtures/spec-generator'

/* ------------------------------------------------------------------------------- building blocks */

/** Every list that takes one item from each of `lists`, in order. */
const product = <T>(lists: ReadonlyArray<readonly T[]>): T[][] =>
  lists.reduce<T[][]>(
    (prefixes, list) => prefixes.flatMap((prefix) => list.map((item) => [...prefix, item])),
    [[]],
  )

/** `count` copies of `list`, for `product`. */
const times = <T>(list: readonly T[], count: number): Array<readonly T[]> =>
  Array.from({ length: count }, () => list)

/** The sequences of distinct `items` of length at most `max`, shortest first. */
function arrangements<T>(items: readonly T[], max: number): T[][] {
  const all: T[][] = [[]]
  let level: T[][] = [[]]
  for (let length = 1; length <= max; length += 1) {
    level = level.flatMap((prefix) =>
      items.filter((item) => !prefix.includes(item)).map((item) => [...prefix, item]),
    )
    all.push(...level)
  }
  return all
}

const data = (v: Value): Slot => ({ a: [true, true, true], v })

const object = (
  fields: Array<[string, Slot]>,
  extensible = true,
  prototype: Extract<GraphNode, { kind: 'object' }>['proto'] = 'object',
): GraphNode => ({ extensible, fields, kind: 'object', proto: prototype })

const array = (
  entries: Array<Value | { hole: true }>,
  extensibility: Extensibility = 'extensible',
): GraphNode => ({
  entries,
  ext: extensibility,
  kind: 'array',
})

const EMPTY: GraphNode = object([])

/** What a slot of a listed node holds: a primitive, a fresh node of its own graph by index, or,
 * in a next graph, the current object of a current node, which joins the graph with every current
 * object it reaches. */
type Item = { cur: number } | { fresh: number } | { prim: Value }

const prim = (v: Value): Item => ({ prim: v })
const currentAt = (index: number): Item => ({ cur: index })
const fresh = (index: number): Item => ({ fresh: index })

/** A listed node: its kind and positions, and the item at each position. */
interface RawNode {
  readonly items: readonly Item[]
  readonly shape: Shape
}

interface Shape {
  readonly kind: 'array' | 'object'
  readonly positions: readonly string[]
}

/** The objects with ordered keys from `a` and `b`, and the arrays, of at most `slots` positions. */
const shapes = (slots: number): Shape[] => [
  ...arrangements(['a', 'b'], Math.min(2, slots)).map((keys): Shape => ({
    kind: 'object',
    positions: keys,
  })),
  ...[0, 1, 2]
    .filter((length) => length <= slots)
    .map((length): Shape => ({ kind: 'array', positions: Array.from({ length }, String) })),
]

/** The node of a shape whose positions hold `values`. */
const nodeOf = (shape: Shape, values: readonly Value[]): GraphNode =>
  shape.kind === 'object'
    ? object(shape.positions.map((key, index) => [key, data(values[index])]))
    : array([...values])

/** The node references of a listed node that stay inside its own graph. */
const ownReferences = (node: RawNode, local: 'cur' | 'fresh'): number[] =>
  node.items.flatMap((item) => (local in item ? [(item as Record<string, number>)[local]] : []))

/** Whether every node of a listed graph is reachable from its first. */
function connected(nodes: readonly RawNode[], local: 'cur' | 'fresh'): boolean {
  const seen = new Set([0])
  const pending = [0]
  for (let at = 0; at < pending.length; at += 1)
    for (const next of ownReferences(nodes[pending[at]], local))
      if (!seen.has(next)) {
        seen.add(next)
        pending.push(next)
      }
  return seen.size === nodes.length
}

/** The listed nodes of one combination of shapes, each position filled from `domain`. */
function fill(chosen: readonly Shape[], domain: readonly Item[]): RawNode[][] {
  const sizes = chosen.map((shape) => shape.positions.length)
  const total = sizes.reduce((sum, size) => sum + size, 0)
  return product(times(domain, total)).map((items) => {
    let at = 0
    return chosen.map((shape, index) => ({ items: items.slice(at, (at += sizes[index])), shape }))
  })
}

/** Every connected listed graph of at most `nodes` nodes and `slots` positions in all, each
 * position holding an item of `domain(size)`. */
function graphs(
  nodes: number,
  slots: number,
  domain: (size: number) => readonly Item[],
  local: 'cur' | 'fresh',
): RawNode[][] {
  const result: RawNode[][] = []
  for (let size = 1; size <= nodes; size += 1)
    for (const chosen of product(times(shapes(slots), size)))
      if (chosen.reduce((sum, shape) => sum + shape.positions.length, 0) <= slots)
        result.push(...fill(chosen, domain(size)).filter((raw) => connected(raw, local)))
  return result
}

const reference = (index: number): Value => ({ ref: index })
const primOf = (item: Item, other: (item: Item) => Value): Value =>
  'prim' in item ? item.prim : other(item)

/** The current graph of listed nodes. */
const currentGraph = (raw: readonly RawNode[]): Graph => ({
  nodes: raw.map((node) =>
    nodeOf(
      node.shape,
      node.items.map((item) => primOf(item, (other) => reference((other as { cur: number }).cur))),
    ),
  ),
  root: reference(0),
})

/** A next graph under construction: its nodes, and per node the current node it is. */
class NextGraph {
  private readonly ids = new Map<number, number>()
  readonly nodes: GraphNode[] = []
  readonly same: Array<number | null> = []
  constructor(private readonly current: Graph) {}

  /** The next node that is current node `c`, added with every current object it reaches. */
  of(c: number): number {
    const known = this.ids.get(c)
    if (known !== undefined) return known
    const id = this.add(c)
    this.ids.set(c, id)
    this.nodes[id] = mapReferences(this.current.nodes[c], (v) =>
      isReference(v) ? reference(this.of(v.ref)) : v,
    )
    return id
  }

  /** Adds a node, `same` the current node it is or null, to fill in later. */
  add(same: number | null): number {
    this.same.push(same)
    return this.nodes.push(EMPTY) - 1
  }

  /** The value an item stands for, fresh nodes at `offset` and up. */
  value(item: Item, offset = 0): Value {
    if ('prim' in item) return item.prim
    return 'fresh' in item ? reference(offset + item.fresh) : reference(this.of(item.cur))
  }

  case(classes: Classes = []): Case {
    return {
      classes,
      cur: this.current,
      next: { nodes: this.nodes, root: reference(0) },
      same: this.same,
    }
  }
}

/** The case of a current graph and the fresh next nodes, the first of them the next root. */
function caseOf(current: Graph, freshNodes: readonly RawNode[], classes: Classes = []): Case {
  const next = new NextGraph(current)
  for (const _ of freshNodes) next.add(null)
  freshNodes.forEach((node, index) => {
    next.nodes[index] = nodeOf(
      node.shape,
      node.items.map((item) => next.value(item)),
    )
  })
  return next.case(classes)
}

/** The case whose next root is current node `c`: `next` is a current object, with everything
 * it reaches. */
function rootIsCurrent(current: Graph, c: number): Case {
  const next = new NextGraph(current)
  next.of(c)
  return next.case()
}

/* ------------------------------------------------------------------------------------ universes */

/** Objects and arrays of up to two nodes and two positions on each side: sharing, cycles,
 * reorders, kind changes, current objects in place or elsewhere, and either root inside `next`. */
function structureCases(): Case[] {
  const prims = [prim(0), prim(1)]
  const currents = graphs(
    2,
    2,
    (size) => [...prims, ...Array.from({ length: size }, (_, c) => currentAt(c))],
    'cur',
  )
  return currents.flatMap((raw) => {
    const current = currentGraph(raw)
    const nexts = graphs(
      2,
      2,
      (size) => [
        ...prims,
        ...Array.from({ length: size }, (_, f) => fresh(f)),
        ...raw.map((_, c) => currentAt(c)),
      ],
      'fresh',
    )
    const inner = raw.length > 1 ? [rootIsCurrent(current, 1)] : []
    return [...nexts.map((freshNodes) => caseOf(current, freshNodes)), ...inner]
  })
}

/** The slots a current object can hold at a key, for value `v`: writable or not, configurable or
 * not, and accessors without a setter, configurable or not, with a setter that stores and with
 * one that drops its value. */
const SLOT_KINDS: ReadonlyArray<(v: Value) => Slot> = [
  (v) => ({ a: [true, true, true], v }),
  (v) => ({ a: [false, true, true], v }),
  (v) => ({ a: [true, true, false], v }),
  (v) => ({ a: [false, true, false], v }),
  (v) => ({ c: true, e: true, get: v, set: null }),
  (v) => ({ c: false, e: true, get: v, set: null }),
  (v) => ({ c: true, e: true, get: v, set: true }),
  (v) => ({ c: true, e: true, get: v, set: false }),
]

/** A current root object of every slot kind at `a`, or at `a` then `b`, extensible or not,
 * holding 0 or an empty child object, against every next root of up to two keys holding 0, 1,
 * that child or a fresh empty object. */
function attributeCases(): Case[] {
  return [['a'], ['a', 'b']].flatMap((keys) =>
    product(times(SLOT_KINDS, keys.length)).flatMap((kinds) =>
      product(times<Value>([0, reference(1)], keys.length)).flatMap((values) =>
        [true, false].flatMap((extensible) => attributeCasesOf(keys, kinds, values, extensible)),
      ),
    ),
  )
}

/** The cases of one current root of the attribute universe. */
function attributeCasesOf(
  keys: readonly string[],
  kinds: ReadonlyArray<(v: Value) => Slot>,
  values: readonly Value[],
  extensible: boolean,
): Case[] {
  const root = object(
    keys.map((key, index) => [key, kinds[index](values[index])]),
    extensible,
  )
  const child = values.some(isReference)
  const current: Graph = { nodes: child ? [root, EMPTY] : [root], root: reference(0) }
  return nextRoots(child ? [prim(0), prim(1), currentAt(1)] : [prim(0), prim(1)]).map(
    (freshNodes) => caseOf(current, freshNodes),
  )
}

/** Every next root object of up to two keys holding `items` or a fresh empty object, with that
 * object as a second fresh node when it is used. */
function nextRoots(items: readonly Item[]): RawNode[][] {
  return arrangements(['a', 'b'], 2).flatMap((keys) =>
    product(times([...items, fresh(1)], keys.length)).map((chosen) => {
      const root: RawNode = { items: chosen, shape: { kind: 'object', positions: keys } }
      const empty: RawNode = { items: [], shape: { kind: 'object', positions: [] } }
      return chosen.some((item) => 'fresh' in item) ? [root, empty] : [root]
    }),
  )
}

/** The slots a class prototype can hold: data, an accessor without a setter, with one that
 * stores and with one that drops its value. */
const CLASS_SLOTS: readonly Slot[] = [
  data(0),
  { c: true, e: true, get: 0, set: null },
  { c: true, e: true, get: 0, set: true },
  { c: true, e: true, get: 0, set: false },
]

/** A current root object labelled with a class whose prototype holds one slot at `a` or `b`,
 * with no own key or an own `a`, against every next root of up to two keys holding 0 or 1. */
function classCases(): Case[] {
  return product<unknown>([CLASS_SLOTS, ['a', 'b'], [[], [['a', data(0)]]]]).flatMap(
    ([slot, key, fields]) => {
      const classes: Classes = [[[key as string, slot as Slot]]]
      const root = object(fields as Array<[string, Slot]>, true, { cls: 0 })
      const current: Graph = { nodes: [root], root: reference(0) }
      return arrangements(['a', 'b'], 2).flatMap((keys) =>
        product(times([prim(0), prim(1)], keys.length)).map((chosen) =>
          caseOf(current, [{ items: chosen, shape: { kind: 'object', positions: keys } }], classes),
        ),
      )
    },
  )
}

/** The next value of a collection item: a primitive, the current child or a fresh empty object,
 * which is next node 1. */
const collectionValue = (next: NextGraph, item: Item): Value => next.value(item, 1)

/** A current root `Map` of up to two entries with keys 0, 1 or an empty child object and values 0
 * or that child, against every next root `Map` of up to two entries with keys 0, 1, the child or
 * a fresh empty object and values 0, the child or that fresh object; and the same for `Set`
 * members. */
function collectionCases(): Case[] {
  const currentKeys = [prim(0), prim(1), currentAt(1)]
  const nextKeys = [prim(0), prim(1), currentAt(1), fresh(0)]
  const maps = arrangements(currentKeys, 2).flatMap((keys) =>
    product(times([prim(0), currentAt(1)], keys.length)).flatMap((values) =>
      collectionCasesOf(keys, values, nextKeys, (k, v) => ({
        entries: k.map((key, index): [Value, Value] => [key, v[index]]),
        kind: 'map',
      })),
    ),
  )
  const sets = arrangements(currentKeys, 2).flatMap((members) =>
    collectionCasesOf(members, undefined, nextKeys, (k) => ({ kind: 'set', members: k })),
  )
  return [...maps, ...sets]
}

/** The cases of one current collection against every next collection over `nextKeys`, values
 * drawn like keys without 1 when the kind has values. */
function collectionCasesOf(
  keys: readonly Item[],
  values: readonly Item[] | undefined,
  nextKeys: readonly Item[],
  build: (keys: Value[], values: Value[]) => GraphNode,
): Case[] {
  const items = [...keys, ...(values ?? [])]
  const child = items.some((item) => 'cur' in item)
  const plain = (item: Item): Value => primOf(item, () => reference(1))
  const current: Graph = {
    nodes: [build(keys.map(plain), (values ?? []).map(plain)), ...(child ? [EMPTY] : [])],
    root: reference(0),
  }
  const usable = nextKeys.filter((item) => child || !('cur' in item))
  const nextValues = usable.filter((item) => !('prim' in item) || item.prim !== 1)
  return arrangements(usable, 2).flatMap((k) =>
    product(times(nextValues, values === undefined ? 0 : k.length)).map((v) => {
      const next = new NextGraph(current)
      next.add(null)
      const usesFresh = [...k, ...v].some((item) => 'fresh' in item)
      if (usesFresh) next.add(null)
      next.nodes[0] = build(
        k.map((item) => collectionValue(next, item)),
        v.map((item) => collectionValue(next, item)),
      )
      return next.case()
    }),
  )
}

const HOLE = { hole: true } as const
const ENTRIES = [0, 1, HOLE] as const

/** A current root array of up to two entries, holes included, at each integrity level, against
 * every next root array of up to three entries. */
function arrayCases(): Case[] {
  const lists = (max: number) =>
    [0, 1, 2, 3]
      .filter((length) => length <= max)
      .flatMap((length) => product(times(ENTRIES, length)))
  return product<unknown>([lists(2), ['extensible', 'nonExtensible', 'sealed', 'frozen']]).flatMap(
    ([entries, extensibility]) =>
      lists(3).map((nextEntries): Case => ({
        classes: [],
        cur: {
          nodes: [array(entries as Array<Value | { hole: true }>, extensibility as Extensibility)],
          root: reference(0),
        },
        next: { nodes: [array(nextEntries)], root: reference(0) },
        same: [null],
      })),
  )
}

const date = (ms: number): GraphNode => ({ kind: 'date', ms })

/** Dates as roots and at a key: kept with a new time, in place, or against an object. */
function dateCases(): Case[] {
  const roots = product([
    [0, 1000],
    [0, 1000],
  ]).map(([a, b]): Case => ({
    classes: [],
    cur: { nodes: [date(a)], root: reference(0) },
    next: { nodes: [date(b)], root: reference(0) },
    same: [null],
  }))
  const keyed = [0, 1000].flatMap((ms) => {
    const current: Graph = {
      nodes: [object([['a', data(reference(1))]]), date(ms)],
      root: reference(0),
    }
    const nexts: GraphNode[][] = [[date(0)], [date(1000)], [EMPTY]]
    return [
      ...nexts.map((child) => {
        const next = new NextGraph(current)
        next.add(null)
        next.add(null)
        next.nodes[0] = object([['a', data(reference(1))]])
        next.nodes[1] = child[0]
        return next.case()
      }),
      caseOf(current, [{ items: [currentAt(1)], shape: { kind: 'object', positions: ['a'] } }]),
    ]
  })
  return [...roots, ...keyed]
}

/** The buffers of the binary universe: empty, one byte of either value, two bytes, and one
 * resizable byte. */
const BUFFERS: ReadonlyArray<Extract<GraphNode, { kind: 'buffer' }>> = [
  { bytes: [], kind: 'buffer', max: null },
  { bytes: [0], kind: 'buffer', max: null },
  { bytes: [1], kind: 'buffer', max: null },
  { bytes: [0, 0], kind: 'buffer', max: null },
  { bytes: [0], kind: 'buffer', max: 2 },
]

const view = (
  buffer: number,
  ctor: ViewConstructor,
  offset: number,
  length: number,
): GraphNode => ({
  buffer: reference(buffer),
  ctor,
  kind: 'view',
  length,
  offset,
})

/** The views of the binary universe over a buffer of `size` bytes at node `buffer`: whole
 * `Uint8Array` and `DataView` views, a whole `Int16Array` view over an even length, and a
 * one-byte `Uint8Array` view at offset 1 of two bytes. */
const viewsOver = (buffer: number, size: number): GraphNode[] => [
  view(buffer, 'Uint8Array', 0, size),
  view(buffer, 'DataView', 0, size),
  ...(size % 2 === 0 ? [view(buffer, 'Int16Array', 0, size)] : []),
  ...(size === 2 ? [view(buffer, 'Uint8Array', 1, 1)] : []),
]

/** A buffer at `a`, a buffer at `a` with a view over it at `b`, or a view alone at `v`, against
 * every next root of the same layouts over a fresh buffer or the current one, with a fresh view
 * or the current one. */
function binaryCases(): Case[] {
  return BUFFERS.flatMap((buffer) => {
    const size = buffer.bytes.length
    const currents: Graph[] = [
      { nodes: [object([['a', data(reference(1))]]), buffer], root: reference(0) },
      ...viewsOver(1, size).flatMap((v): Graph[] => [
        {
          nodes: [
            object([
              ['a', data(reference(1))],
              ['b', data(reference(2))],
            ]),
            buffer,
            v,
          ],
          root: reference(0),
        },
        { nodes: [object([['v', data(reference(2))]]), buffer, v], root: reference(0) },
      ]),
    ]
    return [...currents.flatMap((current) => binaryNexts(current)), ...twoBufferCases(buffer)]
  })
}

/** A buffer at `a` and a view over another buffer of its length at `b`, so that the view's
 * candidate demands its own buffer at the node `next` may also hold at `a`: against every next
 * root with a buffer at `a`, fresh or either current one, and at `b` a fresh whole `Uint8Array`
 * view over it or the current view. */
function twoBufferCases(buffer: Extract<GraphNode, { kind: 'buffer' }>): Case[] {
  const size = buffer.bytes.length
  const current: Graph = {
    nodes: [
      object([
        ['a', data(reference(1))],
        ['b', data(reference(3))],
      ]),
      buffer,
      { ...buffer, bytes: [...buffer.bytes] },
      view(2, 'Uint8Array', 0, size),
    ],
    root: reference(0),
  }
  return [buffer, currentAt(1), currentAt(2)].flatMap((choice) => {
    const views: Array<GraphNode | Item> = [
      view(-1, 'Uint8Array', 0, size),
      ...(isItem(choice) && 'cur' in choice && choice.cur === 2 ? [currentAt(3)] : []),
    ]
    return views.map((v) => binaryCase(current, choice, v, ['a', 'b']))
  })
}

const isItem = (value: GraphNode | Item): value is Item => !('kind' in value)

/** Every next root of the binary layouts against `current`. */
function binaryNexts(current: Graph): Case[] {
  const choices = [...BUFFERS.map((b): GraphNode | Item => b), currentAt(1)]
  return choices.flatMap((choice) => [
    binaryCase(current, choice, undefined, ['a']),
    ...viewChoices(current, choice).flatMap((v) => [
      binaryCase(current, choice, v, ['a', 'b']),
      binaryCase(current, choice, v, ['v']),
    ]),
  ])
}

/** The views a next root of the binary universe can hold over a buffer choice: fresh views over
 * it, and the current view when the choice is the current buffer and `current` has a view. */
function viewChoices(current: Graph, choice: GraphNode | Item): Array<GraphNode | Item> {
  const own = isItem(choice)
  const size = ((own ? current.nodes[1] : choice) as NodeOf<'buffer'>).bytes.length
  return [...viewsOver(-1, size), ...(own && current.nodes.length > 2 ? [currentAt(2)] : [])]
}

/** One binary case: the next root holds the buffer choice at `a` when `keys` names it, and the
 * view choice at `b` or `v`; a fresh view's buffer is the chosen buffer. */
function binaryCase(
  current: Graph,
  buffer: GraphNode | Item,
  v: GraphNode | Item | undefined,
  keys: readonly string[],
): Case {
  const next = new NextGraph(current)
  next.add(null)
  const bufferId = placed(next, buffer, (node) => node)
  const fields: Array<[string, Slot]> = keys.includes('a') ? [['a', data(reference(bufferId))]] : []
  if (v !== undefined) {
    const viewId = placed(next, v, (node) => ({
      ...(node as NodeOf<'view'>),
      buffer: reference(bufferId),
    }))
    fields.push([keys.includes('b') ? 'b' : 'v', data(reference(viewId))])
  }
  next.nodes[0] = object(fields)
  return next.case()
}

/** The next node of a binary choice: the current object an item names, or a fresh node built
 * from the chosen node. */
function placed(
  next: NextGraph,
  choice: GraphNode | Item,
  build: (node: GraphNode) => GraphNode,
): number {
  if (isItem(choice)) return next.of((choice as { cur: number }).cur)
  const id = next.add(null)
  next.nodes[id] = build(choice)
  return id
}

/** What a next slot of the holder universe holds: an item, a fresh empty object `X` or a fresh
 * holder `G` of one value at `f`. */
type HolderItem = 'G' | 'X' | Item

/** The holders of one value at `f` that the decision cannot write: a frozen data property, a
 * getter without a setter, and the element of a frozen array. */
const HOLDERS: ReadonlyArray<(v: Value) => GraphNode> = [
  (v) => object([['f', { a: [false, true, false], v }]]),
  (v) => object([['f', { c: true, e: true, get: v, set: null }]]),
  (v) => array([v], 'frozen'),
]

/** Fixed slots that hold objects, so that a holder's candidate demands an object at another
 * node: a current root `{ a: Y, b: H }` or `{ a: H, b: Y }`, where the holder `H` holds `Y`,
 * another empty object `Z` or 0, against every next root whose `a` and `b` hold 0, a fresh empty
 * object `X`, a fresh holder `G` of `X`, `Y`, `Z` or 0, or a current object. */
function holderCases(): Case[] {
  return product<unknown>([HOLDERS, [reference(1), reference(3), 0], [false, true]]).flatMap(
    ([holder, held, swapped]) =>
      holderCasesOf(
        (holder as (v: Value) => GraphNode)(held as Value),
        held as Value,
        swapped === true,
      ),
  )
}

const holdsZ = (held: Value): boolean => isReference(held) && held.ref === 3

/** The cases of one current root of the holder universe: `holder` holds `held`, at `b` unless
 * `swapped`. */
function holderCasesOf(holder: GraphNode, held: Value, swapped: boolean): Case[] {
  // A holder of the other empty object `Z` brings it in as current node 3.
  const extra = holdsZ(held) ? [EMPTY] : []
  const keys = swapped ? ['b', 'a'] : ['a', 'b']
  const current: Graph = {
    nodes: [
      object([
        [keys[0], data(reference(1))],
        [keys[1], data(reference(2))],
      ]),
      EMPTY,
      holder,
      ...extra,
    ],
    root: reference(0),
  }
  const others = extra.map((): HolderItem => currentAt(3))
  const items: HolderItem[] = [prim(0), 'X', 'G', currentAt(1), currentAt(2), ...others]
  const heldItems: HolderItem[] = [prim(0), 'X', currentAt(1), ...others]
  return product<HolderItem>([items, items]).flatMap(([a, b]) =>
    (a === 'G' || b === 'G' ? heldItems : [prim(0)]).map((g) =>
      holderCase(current, holder, a, b, g),
    ),
  )
}

/** One case of the holder universe; `G` takes the holder's kind. */
function holderCase(
  current: Graph,
  holder: GraphNode,
  a: HolderItem,
  b: HolderItem,
  g: HolderItem,
): Case {
  const next = new NextGraph(current)
  next.add(null)
  const ids = new Map<'G' | 'X', number>()
  const valueOf = (item: HolderItem): Value => {
    if (typeof item !== 'string') return next.value(item)
    let id = ids.get(item)
    if (id === undefined) ids.set(item, (id = next.add(null)))
    next.nodes[id] = item === 'X' ? EMPTY : refill(holder, valueOf(g))
    return reference(id)
  }
  next.nodes[0] = object([
    ['a', data(valueOf(a))],
    ['b', data(valueOf(b))],
  ])
  return next.case()
}

/** A writable copy of a holder's kind holding `v`. */
const refill = (holder: GraphNode, v: Value): GraphNode =>
  holder.kind === 'array' ? array([v]) : object([['f', data(v)]])

/* ---------------------------------------------------------------------------------- produce */

/** A simulated draft heap: the nodes, and the created objects so far. */
interface Heap {
  readonly created: number
  readonly nodes: readonly GraphNode[]
}

/** The operations a draft of each kind of node accepts, writing values of `values`. */
const OPS: ByKind<[id: number, values: readonly Value[]], Op[]> = {
  array: (node, id, values) => arrayOps(node, id, values),
  buffer: () => [],
  date: (_node, id) => [{ ms: 1000, node: id, op: 'setTime' }],
  map: (node, id, values) => [
    ...product([[0, 1], values]).map(([key, value]): Op => ({
      key,
      node: id,
      op: 'mapSet',
      value,
    })),
    ...node.entries.map(([key]): Op => ({ key, node: id, op: 'mapDelete' })),
  ],
  object: (node, id, values) => objectOps(node, id, values),
  set: (node, id, values) => [
    ...values.map((value): Op => ({ node: id, op: 'setAdd', value })),
    ...node.members.map((value): Op => ({ node: id, op: 'setDelete', value })),
  ],
  view: () => [],
}

/** Each operation a draft of node `id` accepts on `heap`, writing values of `values`. */
const opsFor = (heap: Heap, id: number, values: readonly Value[]): Op[] =>
  byKind(OPS, heap.nodes[id], id, values)

/** Sets of writable keys and of absent keys of an extensible object, and deletions of
 * configurable keys. */
function objectOps(
  node: Extract<GraphNode, { kind: 'object' }>,
  id: number,
  values: readonly Value[],
): Op[] {
  const slotOf = (key: string) => node.fields.find(([k]) => k === key)?.[1]
  const settable = ['a', 'b', 'c'].filter((key) => {
    const slot = slotOf(key)
    return slot === undefined ? node.extensible : 'v' in slot && slot.a[0]
  })
  const deletable = node.fields.filter(([, slot]) => ('v' in slot ? slot.a[2] : slot.c))
  return [
    ...product<unknown>([settable, values]).map(([key, value]): Op => ({
      key: key as string,
      node: id,
      op: 'setKey',
      value: value as Value,
    })),
    ...deletable.map(([key]): Op => ({ key, node: id, op: 'deleteKey' })),
  ]
}

/** Writes to an array draft its integrity level allows: an element at a present index, or at
 * any index up to its length when it can grow; and a length of 0 or one more, where allowed. */
function arrayOps(
  node: Extract<GraphNode, { kind: 'array' }>,
  id: number,
  values: readonly Value[],
): Op[] {
  if (node.ext === 'frozen') return []
  const grows = node.ext === 'extensible'
  const indices = Array.from({ length: node.entries.length + 1 }, (_, index) => index).filter(
    (index) => grows || (index < node.entries.length && !isHole(node.entries[index])),
  )
  const lengths = node.ext === 'sealed' ? [] : [0, node.entries.length + 1]
  return [
    ...product<unknown>([indices, values]).map(([index, value]): Op => ({
      index: index as number,
      node: id,
      op: 'setIndex',
      value: value as Value,
    })),
    ...lengths.map((length): Op => ({ length, node: id, op: 'setLength' })),
  ]
}

/** The heap after `op`. */
function applyOp(heap: Heap, op: Op): Heap {
  if (op.op === 'create') return { created: heap.created + 1, nodes: [...heap.nodes, op.obj] }
  const nodes = [...heap.nodes]
  nodes[op.node] = applied(nodes[op.node], op)
  return { created: heap.created, nodes }
}

const sameValue = (a: unknown, b: unknown): boolean => JSON.stringify(a) === JSON.stringify(b)

type Write = Exclude<Op, { op: 'create' }>

/** `entries` with `value` at `index`, holes filling any gap. */
function withEntry(
  entries: NodeOf<'array'>['entries'],
  index: number,
  value: Value,
): NodeOf<'array'>['entries'] {
  const copy = [...entries]
  while (copy.length <= index) copy.push(HOLE)
  copy[index] = value
  return copy
}

/** `entries` cut, or padded with holes, to `length`. */
function withLength(
  entries: NodeOf<'array'>['entries'],
  length: number,
): NodeOf<'array'>['entries'] {
  const copy = entries.slice(0, length)
  while (copy.length < length) copy.push(HOLE)
  return copy
}

/** `fields` with `key` holding `value`: its own slot when present, else a data property added. */
const withKey = (
  fields: NodeOf<'object'>['fields'],
  key: string,
  value: Value,
): NodeOf<'object'>['fields'] =>
  fields.some(([k]) => k === key)
    ? fields.map(([k, slot]): [string, Slot] =>
        k === key && 'v' in slot ? [k, { a: slot.a, v: value }] : [k, slot],
      )
    : [...fields, [key, data(value)]]

/** `entries` with `key` mapped to `value`: in its place when present, else appended. */
const withMapEntry = (
  entries: NodeOf<'map'>['entries'],
  key: Value,
  value: Value,
): NodeOf<'map'>['entries'] =>
  entries.some(([k]) => sameValue(k, key))
    ? entries.map(([k, v]): [Value, Value] => [k, sameValue(k, key) ? value : v])
    : [...entries, [key, value]]

/** The node after each kind of write to it, as the draft performs it. */
const APPLIERS: {
  [K in Write['op']]: (node: GraphNode, op: Extract<Write, { op: K }>) => GraphNode
} = {
  deleteKey: (node, op) => ({
    ...(node as NodeOf<'object'>),
    fields: (node as NodeOf<'object'>).fields.filter(([k]) => k !== op.key),
  }),
  mapDelete: (node, op) => ({
    ...(node as NodeOf<'map'>),
    entries: (node as NodeOf<'map'>).entries.filter(([k]) => !sameValue(k, op.key)),
  }),
  mapSet: (node, op) => ({
    ...(node as NodeOf<'map'>),
    entries: withMapEntry((node as NodeOf<'map'>).entries, op.key, op.value),
  }),
  setAdd: (node, op) => {
    const set = node as NodeOf<'set'>
    return set.members.some((m) => sameValue(m, op.value))
      ? set
      : { ...set, members: [...set.members, op.value] }
  },
  setByte: (node, op) => ({
    ...(node as NodeOf<'buffer'>),
    bytes: (node as NodeOf<'buffer'>).bytes.map((byte, index) =>
      index === op.index ? op.byte : byte,
    ),
  }),
  setDelete: (node, op) => ({
    ...(node as NodeOf<'set'>),
    members: (node as NodeOf<'set'>).members.filter((m) => !sameValue(m, op.value)),
  }),
  setIndex: (node, op) => ({
    ...(node as NodeOf<'array'>),
    entries: withEntry((node as NodeOf<'array'>).entries, op.index, op.value),
  }),
  setKey: (node, op) => ({
    ...(node as NodeOf<'object'>),
    fields: withKey((node as NodeOf<'object'>).fields, op.key, op.value),
  }),
  setLength: (node, op) => ({
    ...(node as NodeOf<'array'>),
    entries: withLength((node as NodeOf<'array'>).entries, op.length),
  }),
  setTime: (node, op) => ({ ...(node as NodeOf<'date'>), ms: op.ms }),
}

/** The node after a write `op` to it. */
const applied = (node: GraphNode, op: Write): GraphNode =>
  (APPLIERS[op.op] as (node: GraphNode, op: Write) => GraphNode)(node, op)

/** Every operation on `heap`: a write to a draft of a current node reachable as one, writing 0 or
 * a draft or created object, or an empty object created. */
function nextOps(heap: Heap, drafts: readonly number[], size: number): Op[] {
  const created = Array.from({ length: heap.created }, (_, k) => size + k)
  const values: Value[] = [0, ...[...drafts, ...created].map(reference)]
  return [...drafts.flatMap((id) => opsFor(heap, id, values)), { obj: EMPTY, op: 'create' }]
}

/** Every recipe of at most `length` operations over `current`, returning the root draft; those of
 * at most one operation also return 0, another draft or a created object, or `current` itself. */
function recipesOver(current: Graph, length: number): Recipe[] {
  const paths = draftPaths(current)
  const drafts = [...paths.keys()]
  const size = current.nodes.length
  const recipes: Recipe[] = []
  const walk = (heap: Heap, ops: Op[]): void => {
    recipes.push({ cur: current, ops, paths, returns: reference(0), returnsCurrent: false })
    if (ops.length <= 1) recipes.push(...otherReturns(current, ops, paths, heap, drafts))
    if (ops.length < length)
      for (const op of nextOps(heap, drafts, size)) walk(applyOp(heap, op), [...ops, op])
  }
  walk({ created: 0, nodes: current.nodes }, [])
  return recipes
}

/** The recipes of `ops` that return something other than the root draft. */
function otherReturns(
  current: Graph,
  ops: Op[],
  paths: Recipe['paths'],
  heap: Heap,
  drafts: readonly number[],
): Recipe[] {
  const size = current.nodes.length
  const others = [
    ...drafts.filter((id) => id !== 0),
    ...Array.from({ length: heap.created }, (_, k) => size + k),
  ]
  return [
    { cur: current, ops, paths, returns: 0, returnsCurrent: false },
    { cur: current, ops, paths, returns: reference(0), returnsCurrent: true },
    ...others.map((id): Recipe => ({
      cur: current,
      ops,
      paths,
      returns: reference(id),
      returnsCurrent: false,
    })),
  ]
}

/** Every recipe of up to two operations over the current graphs of the structure universe and
 * over a `Map`, a `Set` and a date. */
function produceCases(): Recipe[] {
  const prims = [prim(0), prim(1)]
  const structures = graphs(
    2,
    2,
    (size) => [...prims, ...Array.from({ length: size }, (_, c) => currentAt(c))],
    'cur',
  ).map(currentGraph)
  const collections: Graph[] = [
    { nodes: [{ entries: [[0, 0]], kind: 'map' }], root: reference(0) },
    { nodes: [{ kind: 'set', members: [0] }], root: reference(0) },
    { nodes: [date(0)], root: reference(0) },
  ]
  return [...structures, ...collections].flatMap((graph) => recipesOver(graph, 2))
}

/** Every recipe of up to two operations over a root object with data slots of each attribute
 * kind at `a`, or at `a` and `b`, extensible or not, and over a root array of up to two entries
 * at each integrity level. */
function produceAttributeCases(): Recipe[] {
  const kinds = SLOT_KINDS.slice(0, 4)
  const objects = [['a'], ['a', 'b']].flatMap((keys) =>
    product<unknown>([...times(kinds, keys.length), [true, false]]).map((choice): Graph => ({
      nodes: [
        object(
          keys.map((key, index) => [key, (choice[index] as (v: Value) => Slot)(0)]),
          choice[keys.length] as boolean,
        ),
      ],
      root: reference(0),
    })),
  )
  const arrays = product<unknown>([
    [[], [0], [HOLE], [0, 0], [0, HOLE]],
    ['extensible', 'nonExtensible', 'sealed', 'frozen'],
  ]).map(([entries, extensibility]): Graph => ({
    nodes: [array(entries as Value[], extensibility as Extensibility)],
    root: reference(0),
  }))
  return [...objects, ...arrays].flatMap((graph) => recipesOver(graph, 2))
}

/* -------------------------------------------------------------------------------------- running */

/** The reconcile universes, by name. */
const RECONCILE: Record<string, () => Case[]> = {
  arrays: arrayCases,
  attributes: attributeCases,
  binary: binaryCases,
  classes: classCases,
  collections: collectionCases,
  dates: dateCases,
  holders: holderCases,
  structure: structureCases,
}

const PRODUCE: Record<string, () => Recipe[]> = {
  'produce-attributes': produceAttributeCases,
  'produce-structure': produceCases,
}

const CHUNK = 4000

/** Runs `run` on `cases` in chunks of `CHUNK`, numbering each report by its case's index. */
async function chunked<T, R extends { seed: number }>(
  cases: readonly T[],
  run: (chunk: T[]) => Promise<R[]>,
): Promise<R[]> {
  const reports: R[] = []
  for (let from = 0; from < cases.length; from += CHUNK)
    for (const report of await run(cases.slice(from, from + CHUNK)))
      reports.push({ ...report, seed: report.seed + from })
  return reports
}

interface Universe {
  readonly cases: number
  readonly name: string
  readonly reports: ReadonlyArray<{ check: string; detail: string; seed: number }>
  readonly show: (index: number) => string
}

/** Labels a report with the check that made it. */
const label = (check: string) => (r: { detail: string; seed: number }) => ({ ...r, check })

async function runReconcile(name: string, oracle: Oracle, library: Library): Promise<Universe> {
  const cases = RECONCILE[name]()
  // One oracle request per chunk serves the plain comparison and the one through recording proxies.
  const compared = await chunked(cases, async (chunk) =>
    (await checkCases(reconcileCheck, oracle, chunk, [false, true])).flatMap((list, mode) =>
      list.map(label(mode === 0 ? 'result' : 'writes')),
    ),
  )
  const phases = await chunked(
    cases,
    async (chunk) => (await checkPhaseCases(library, oracle, chunk)).reports,
  )
  return {
    cases: cases.length,
    name,
    reports: [...compared, ...phases.map(label('phases'))],
    show: (index) => reconcileCheck.show(cases[index]),
  }
}

async function runCopies<T>(
  name: string,
  check: Check<T>,
  cases: readonly T[],
  oracle: Oracle,
): Promise<Universe> {
  const reports = await chunked(cases, async (chunk) => (await checkCases(check, oracle, chunk))[0])
  return {
    cases: cases.length,
    name,
    reports: reports.map((r: Report) => ({ ...r, check: name })),
    show: (index) => check.show(cases[index]),
  }
}

/** The distinct current graphs of every reconcile universe, for snapshot. */
const snapshotCases = (): Graph[] => {
  const seen = new Map<string, Graph>()
  for (const make of Object.values(RECONCILE))
    for (const c of make()) seen.set(JSON.stringify(c.cur), c.cur)
  return [...seen.values()]
}

async function runAll(oracle: Oracle, only: string | undefined): Promise<Universe[]> {
  const library = await instrumented()
  const selected = (name: string) => only === undefined || only === name
  const universes: Universe[] = []
  for (const name of Object.keys(RECONCILE).filter(selected))
    universes.push(await runReconcile(name, oracle, library))
  for (const [name, make] of Object.entries(PRODUCE).filter(([n]) => selected(n)))
    universes.push(await runCopies(name, produceCheck, make(), oracle))
  if (selected('snapshot'))
    universes.push(await runCopies('snapshot', snapshotCheck, snapshotCases(), oracle))
  return universes
}

const describe = (u: Universe): string =>
  `${u.name} ${u.cases} (${u.reports.length === 0 ? 'agree' : `${u.reports.length} differences`})`

/** Every universe in `scripts/check/lean.ts`: every difference fails. */
export async function checkSpecEnumerationGate(oracle: Oracle): Promise<void> {
  const universes = await runAll(oracle, undefined)
  const reports = universes.flatMap((u) =>
    u.reports
      .slice(0, 3)
      .map((r) => `${u.name} ${r.check} #${r.seed}: ${r.detail}\n${u.show(r.seed)}`),
  )
  assert.deepEqual(reports, [], 'Spec enumeration differs')
  console.log(`Spec enumeration: ${universes.map(describe).join(', ')}`)
}

if (process.argv[1]?.endsWith('scripts/check/bridges/spec-enumeration.ts')) {
  const { values } = parseArgs({
    options: { count: { default: false, type: 'boolean' }, only: { type: 'string' } },
  })
  if (values.count) {
    for (const [name, make] of [...Object.entries(RECONCILE), ...Object.entries(PRODUCE)])
      console.log(`${name.padEnd(20)} ${make().length}`)
    console.log(`${'snapshot'.padEnd(20)} ${snapshotCases().length}`)
  } else {
    const { startOracle } = await import('../oracle')
    const oracle = await startOracle()
    try {
      const started = Date.now()
      const universes = await runAll(oracle.run, values.only)
      for (const u of universes) {
        console.log(describe(u))
        for (const r of u.reports.slice(0, 5))
          console.log(`  ${r.check} #${r.seed}: ${r.detail}\n${u.show(r.seed)}`)
      }
      console.log(`${Math.round((Date.now() - started) / 1000)} s`)
      if (universes.some((u) => u.reports.length > 0)) process.exitCode = 1
    } finally {
      await oracle.close()
    }
  }
}
