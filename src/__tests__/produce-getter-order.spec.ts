import { assert, it } from 'vitest'
import { produce } from '../index'

// README (`produce`): after the recipe returns, each own getter in the result is called once, in
// depth-first order. Lean: Produce.GetterOrder.

/** What a slot holds: a node of the graph, by index, or a primitive. */
type Child = number | { readonly primitive: number }

/** An own property of an object or an array element; a getter returns its child. */
interface Slot {
  readonly child: Child
  readonly getter: boolean
}

/** A node: an object or array with slots, or a `Map` (key, value, key, value, …) or `Set`. */
interface Node {
  readonly kind: 'array' | 'map' | 'object' | 'set'
  readonly slots: readonly Slot[]
}

/** The recipe's change: none, or a new entry added to one node through the draft. */
type Change = number | undefined

const data = (child: Child): Slot => ({ child, getter: false })
const getter = (child: Child): Slot => ({ child, getter: true })
const primitive = (value: number): Child => ({ primitive: value })

/** The key of slot `index` of an object; letters keep insertion order as own-key order. */
const keyOf = (index: number): string => String.fromCharCode(97 + index)

/** The key of slot `position` of an object or array. */
const slotKey = (node: Node, position: number): string =>
  node.kind === 'array' ? String(position) : keyOf(position)

/** The getter calls, logged as `node.key` while `recording` is set. */
interface Log {
  calls: string[]
  recording: boolean
}

/** An empty node of each kind. */
const empty: Readonly<Record<Node['kind'], () => unknown>> = {
  array: () => [],
  map: () => new Map(),
  object: () => ({}),
  set: () => new Set(),
}

/** Adds a `Map`'s entries, from its slots in key and value pairs, or a `Set`'s members. */
function fillCollection(
  target: Map<unknown, unknown> & Set<unknown>,
  node: Node,
  resolve: (child: Child) => unknown,
): void {
  if (node.kind === 'map')
    for (let slot = 0; slot + 1 < node.slots.length; slot += 2)
      target.set(resolve(node.slots[slot].child), resolve(node.slots[slot + 1].child))
  else for (const slot of node.slots) target.add(resolve(slot.child))
}

/** Defines the slots of object or array `index`; each getter logs `index.key`. */
function fillProperties(
  target: Record<string, unknown>,
  index: number,
  node: Node,
  resolve: (child: Child) => unknown,
  log: Log,
): void {
  for (const [position, slot] of node.slots.entries()) {
    const key = slotKey(node, position)
    const label = `${index}.${key}`
    if (slot.getter)
      Object.defineProperty(target, key, {
        configurable: true,
        enumerable: true,
        get() {
          if (log.recording) log.calls.push(label)
          return resolve(slot.child)
        },
      })
    else target[key] = resolve(slot.child)
  }
}

/** Builds the graph; each getter logs `node.key` while `log.recording` is set. */
function build(nodes: readonly Node[], log: Log): unknown[] {
  const built = nodes.map((node) => empty[node.kind]())
  const resolve = (child: Child): unknown =>
    typeof child === 'number' ? built[child] : child.primitive
  for (const [index, node] of nodes.entries())
    if (node.kind === 'map' || node.kind === 'set')
      fillCollection(built[index] as Map<unknown, unknown> & Set<unknown>, node, resolve)
    else fillProperties(built[index] as Record<string, unknown>, index, node, resolve, log)
  return built
}

/** The slots of a node as finalization lists them: a `Map`'s keys and values, a `Set`'s members,
 * each kept once by the built-in collection. */
function listed(nodes: readonly Node[], built: readonly unknown[], index: number): Slot[] {
  const node = nodes[index]
  if (node.kind === 'object' || node.kind === 'array') return [...node.slots]
  const slots: Slot[] = []
  const of = (value: unknown): Slot => {
    const at = built.indexOf(value)
    return data(at === -1 ? primitive(value as number) : at)
  }
  if (node.kind === 'map')
    for (const [key, value] of built[index] as Map<unknown, unknown>) slots.push(of(key), of(value))
  else for (const member of built[index] as Set<unknown>) slots.push(of(member))
  return slots
}

/** The getters of the graph in depth-first order from node 0: each node is entered once, at its
 * first slot in that order, and its slots are visited in order, each child before the next
 * slot. */
function depthFirst(nodes: readonly Node[], built: readonly unknown[]): string[] {
  const order: string[] = []
  const entered = new Set<number>()
  const enter = (index: number): void => {
    entered.add(index)
    const node = nodes[index]
    for (const [position, slot] of listed(nodes, built, index).entries()) {
      if (slot.getter) order.push(`${index}.${slotKey(node, position)}`)
      if (typeof slot.child === 'number' && !entered.has(slot.child)) enter(slot.child)
    }
  }
  enter(0)
  return order
}

/** The steps from node `index` to its children through an object, an array or a `Map`'s values:
 * each a property key or a `Map` key, with the child it leads to. */
function steps(
  nodes: readonly Node[],
  built: readonly unknown[],
  index: number,
): Array<[unknown, Child]> {
  const node = nodes[index]
  if (node.kind === 'set') return []
  if (node.kind !== 'map')
    return node.slots.map((slot, position) => [slotKey(node, position), slot.child])
  const found: Array<[unknown, Child]> = []
  for (const [key, value] of built[index] as Map<unknown, unknown>) {
    const at = built.indexOf(value)
    if (at !== -1) found.push([key, at])
  }
  return found
}

/** The keys from node 0 to `target`, following each node's parent back. */
function unwind(parents: ReadonlyMap<number, [number, unknown]>, target: number): unknown[] {
  const path: unknown[] = []
  for (let at = target; at !== 0; at = parents.get(at)![0]) path.unshift(parents.get(at)![1])
  return path
}

/** The keys that lead from node 0 to `target` through objects, arrays and `Map` values: a
property key, or a `Map` key; undefined when no such path exists. */
function pathTo(
  nodes: readonly Node[],
  built: readonly unknown[],
  target: number,
): unknown[] | undefined {
  const parents = new Map<number, [number, unknown]>()
  const queue = [0]
  const reached = new Set([0])
  while (queue.length > 0) {
    const index = queue.shift()!
    if (index === target) return unwind(parents, target)
    for (const [key, child] of steps(nodes, built, index)) {
      if (typeof child !== 'number' || reached.has(child)) continue
      reached.add(child)
      parents.set(child, [index, key])
      queue.push(child)
    }
  }
  return undefined
}

/** Runs `produce` with the change, and compares the getter calls after the recipe returns with
 * the depth-first order of the result. */
function check(nodes: readonly Node[], change: Change, label: string): void {
  const log = { calls: [] as string[], recording: false }
  const built = build(nodes, log)
  const path = change === undefined ? undefined : pathTo(nodes, built, change)
  produce(built[0], (draft) => {
    if (path !== undefined) {
      let at: unknown = draft
      for (const key of path)
        at = at instanceof Map ? at.get(key) : (at as Record<string, unknown>)[key as string]
      if (at instanceof Map) at.set('changed', 1)
      else if (at instanceof Set) at.add('changed')
      else if (Array.isArray(at)) at.push(1)
      else (at as Record<string, unknown>).changed = 1
    }
    log.recording = true
    return draft
  })
  // A change adds a primitive entry at the end of its node, which moves no getter.
  const expected = depthFirst(nodes, built)
  assert.deepEqual(log.calls, expected, label)
  assert.equal(new Set(log.calls).size, log.calls.length, `once: ${label}`)
}

/** Every node unchanged, then each node changed in turn. */
function checkAll(nodes: readonly Node[], label: string): void {
  check(nodes, undefined, `${label}, unchanged`)
  for (let index = 0; index < nodes.length; index += 1)
    check(nodes, index, `${label}, node ${index} changed`)
}

it('calls the getters of nested objects once, in depth-first order', () => {
  checkAll(
    [
      { kind: 'object', slots: [data(1), getter(primitive(5)), data(4)] },
      { kind: 'object', slots: [getter(primitive(1)), data(2), getter(primitive(4))] },
      { kind: 'object', slots: [data(3), getter(primitive(2))] },
      { kind: 'object', slots: [getter(primitive(3))] },
      { kind: 'object', slots: [getter(primitive(6))] },
    ],
    'nested objects',
  )
})

it('enters the object a getter returns before the next slot', () => {
  checkAll(
    [
      { kind: 'object', slots: [getter(1), getter(primitive(0)), data(2)] },
      { kind: 'object', slots: [getter(primitive(1)), getter(2)] },
      { kind: 'object', slots: [getter(primitive(2))] },
    ],
    'getter children',
  )
})

it('calls the getters of arrays, Map keys and values and Set members in depth-first order', () => {
  checkAll(
    [
      { kind: 'object', slots: [data(1), data(4), data(7), getter(primitive(9))] },
      { kind: 'array', slots: [data(2), getter(3), data(primitive(0))] },
      { kind: 'object', slots: [getter(primitive(0))] },
      { kind: 'object', slots: [getter(primitive(1))] },
      { kind: 'map', slots: [data(5), data(6), data(primitive(1)), data(2)] },
      { kind: 'object', slots: [getter(primitive(2))] },
      { kind: 'object', slots: [getter(primitive(3))] },
      { kind: 'set', slots: [data(8), data(primitive(4))] },
      { kind: 'object', slots: [getter(primitive(5))] },
    ],
    'collections',
  )
})

it('enters a shared object once, at its first position, and follows cycles back as visited', () => {
  checkAll(
    [
      { kind: 'object', slots: [data(1), data(2), getter(primitive(0))] },
      { kind: 'object', slots: [data(3), getter(2), data(0)] },
      { kind: 'object', slots: [data(3), getter(primitive(1)), data(1)] },
      { kind: 'object', slots: [getter(primitive(2)), getter(0)] },
    ],
    'sharing and cycles',
  )
})

it('calls a getter that returns a draft once, before the slots after it', () => {
  const calls: string[] = []
  let recording = false
  const item = {
    get n() {
      if (recording) calls.push('item.n')
      return 1
    },
  }
  const current = {
    items: [item],
    get first(): unknown {
      if (recording) calls.push('first')
      return (this as { items: unknown[] }).items[0]
    },
    get last() {
      if (recording) calls.push('last')
      return 2
    },
  }
  const result = produce(current, (draft) => {
    recording = true
    return draft
  })
  assert.deepEqual(calls, ['item.n', 'first', 'last'])
  assert.notStrictEqual(result, current)
  assert.strictEqual(result.first, item)
})

/** A seeded generator, so a failure names its graph. */
function random(seed: number): () => number {
  let state = seed >>> 0
  return () => {
    state = (state + 0x6d_2b_79_f5) >>> 0
    let value = state
    value = Math.imul(value ^ (value >>> 15), value | 1)
    value ^= value + Math.imul(value ^ (value >>> 7), value | 61)
    return ((value ^ (value >>> 14)) >>> 0) / 4_294_967_296
  }
}

/** A random integer from 0 to `count - 1`. */
const pick = (next: () => number, count: number): number => Math.floor(next() * count)

const kinds = ['object', 'object', 'object', 'array', 'array', 'map', 'set'] as const

/** A random slot of a node of `kind` among `size` nodes; only an object's or array's can be a
 * getter. */
function randomSlot(next: () => number, kind: Node['kind'], size: number): Slot {
  const child = next() < 0.6 ? pick(next, size) : primitive(pick(next, 3))
  const accessor = (kind === 'object' || kind === 'array') && next() < 0.4
  return accessor ? getter(child) : data(child)
}

/** A random node `index` among `size` nodes; node 0 is more often an object, and a `Map`'s slots
 * come in key and value pairs. */
function randomNode(next: () => number, index: number, size: number): Node {
  const kind = index === 0 && next() < 0.7 ? 'object' : kinds[pick(next, kinds.length)]
  const count = kind === 'map' ? 2 * pick(next, 3) : pick(next, 4)
  const slots: Slot[] = []
  for (let slot = 0; slot < count; slot += 1) slots.push(randomSlot(next, kind, size))
  return { kind, slots }
}

/** A random graph of one to six nodes. */
function randomGraph(next: () => number): Node[] {
  const size = 1 + pick(next, 6)
  const nodes: Node[] = []
  for (let index = 0; index < size; index += 1) nodes.push(randomNode(next, index, size))
  return nodes
}

it('calls the getters of random graphs with sharing and cycles once, in depth-first order', () => {
  for (let seed = 1; seed <= 300; seed += 1) {
    const next = random(seed)
    const nodes = randomGraph(next)
    check(nodes, undefined, `seed ${seed}, unchanged`)
    check(nodes, pick(next, nodes.length), `seed ${seed}, changed`)
  }
})
