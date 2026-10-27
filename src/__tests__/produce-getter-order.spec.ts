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

/** Builds the graph; each getter logs `node.key` while `log.recording` is set. */
function build(nodes: readonly Node[], log: { calls: string[]; recording: boolean }): unknown[] {
  const built: unknown[] = nodes.map((node) =>
    node.kind === 'object'
      ? {}
      : node.kind === 'array'
        ? []
        : node.kind === 'map'
          ? new Map()
          : new Set(),
  )
  const resolve = (child: Child): unknown =>
    typeof child === 'number' ? built[child] : child.primitive
  for (const [index, node] of nodes.entries()) {
    const target = built[index] as Map<unknown, unknown> & Record<string, unknown> & Set<unknown>
    if (node.kind === 'map') {
      for (let slot = 0; slot + 1 < node.slots.length; slot += 2)
        target.set(resolve(node.slots[slot].child), resolve(node.slots[slot + 1].child))
      continue
    }
    if (node.kind === 'set') {
      for (const slot of node.slots) target.add(resolve(slot.child))
      continue
    }
    for (const [position, slot] of node.slots.entries()) {
      const key = node.kind === 'array' ? String(position) : keyOf(position)
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
      if (slot.getter)
        order.push(`${index}.${node.kind === 'array' ? String(position) : keyOf(position)}`)
      if (typeof slot.child === 'number' && !entered.has(slot.child)) enter(slot.child)
    }
  }
  enter(0)
  return order
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
    if (index === target) {
      const path: unknown[] = []
      for (let at = target; at !== 0; at = parents.get(at)![0]) path.unshift(parents.get(at)![1])
      return path
    }
    const node = nodes[index]
    const steps: Array<[unknown, Child]> = []
    if (node.kind === 'map')
      for (const [key, value] of built[index] as Map<unknown, unknown>) {
        const at = built.indexOf(value)
        if (at !== -1) steps.push([key, at])
      }
    else if (node.kind !== 'set')
      for (const [position, slot] of node.slots.entries())
        steps.push([node.kind === 'array' ? String(position) : keyOf(position), slot.child])
    for (const [key, child] of steps) {
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

it('calls the getters of random graphs with sharing and cycles once, in depth-first order', () => {
  const kinds = ['object', 'object', 'object', 'array', 'array', 'map', 'set'] as const
  for (let seed = 1; seed <= 300; seed += 1) {
    const next = random(seed)
    const pick = (count: number): number => Math.floor(next() * count)
    const size = 1 + pick(6)
    const nodes: Node[] = []
    for (let index = 0; index < size; index += 1) {
      const kind = index === 0 && next() < 0.7 ? 'object' : kinds[pick(kinds.length)]
      const count = kind === 'map' ? 2 * pick(3) : pick(4)
      const slots: Slot[] = []
      for (let slot = 0; slot < count; slot += 1) {
        const child = next() < 0.6 ? pick(size) : primitive(pick(3))
        const accessor = (kind === 'object' || kind === 'array') && next() < 0.4
        slots.push(accessor ? getter(child) : data(child))
      }
      nodes.push({ kind, slots })
    }
    check(nodes, undefined, `seed ${seed}, unchanged`)
    check(nodes, pick(size), `seed ${seed}, changed`)
  }
})
