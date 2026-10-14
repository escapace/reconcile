import { assert } from 'vitest'
import { reactive } from 'vue'

// Fixed seeds and counts preserve the temporary fuzzers' workloads. Each case
// reports its starting PRNG state so a failure can be reproduced independently.
export function randomSource(seed: number, shift = 0) {
  return {
    next: (limit: number): number => {
      seed = (Math.imul(seed, 1_664_525) + 1_013_904_223) >>> 0
      return (seed >>> shift) % limit
    },
    get seed(): number {
      return seed
    },
  }
}

export function checkCase<T>(context: object, run: () => T): T {
  try {
    return run()
  } catch (cause) {
    throw new Error(`Fuzz case: ${JSON.stringify(context)}`, { cause })
  }
}

// Independent ordered graph comparison: both maps are needed to reject both
// splitting one alias and merging two distinct objects. Binary views also compare
// their complete backing storage, not just the bytes visible through the view.
export function graphsEqual(expected: unknown, actual: unknown): boolean {
  const images = new Map<object, object>()
  const owners = new Set<object>()
  const visit = (left: unknown, right: unknown): boolean => {
    if (typeof left !== 'object' || left === null) return Object.is(left, right)
    if (typeof right !== 'object' || right === null) return false
    if (images.has(left)) return images.get(left) === right
    if (owners.has(right) || left.constructor !== right.constructor) return false
    images.set(left, right)
    owners.add(right)
    return contentsEqual(left, right, visit)
  }
  return visit(expected, actual)
}

type GraphVisit = (left: unknown, right: unknown) => boolean

// Compares a newly paired object's contents; `visit` pairs and compares its children.
function contentsEqual(left: object, right: object, visit: GraphVisit): boolean {
  if (left instanceof Date)
    return right instanceof Date && Object.is(left.getTime(), right.getTime())
  if (left instanceof ArrayBuffer) return buffersEqual(left, right)
  if (ArrayBuffer.isView(left)) return viewsEqual(left, right, visit)
  if (left instanceof Map) return mapsEqual(left as Map<unknown, unknown>, right, visit)
  if (left instanceof Set) return setsEqual(left as Set<unknown>, right, visit)
  return propertiesEqual(left, right, visit)
}

function buffersEqual(left: ArrayBuffer, right: object): boolean {
  if (!(right instanceof ArrayBuffer) || left.byteLength !== right.byteLength) return false
  const a = new Uint8Array(left)
  const b = new Uint8Array(right)
  return a.every((value, index) => value === b[index])
}

function viewsEqual(left: ArrayBufferView, right: object, visit: GraphVisit): boolean {
  return (
    ArrayBuffer.isView(right) &&
    left.byteOffset === right.byteOffset &&
    left.byteLength === right.byteLength &&
    visit(left.buffer, right.buffer)
  )
}

function mapsEqual(left: Map<unknown, unknown>, right: object, visit: GraphVisit): boolean {
  if (!(right instanceof Map) || left.size !== right.size) return false
  const entries = (right as Map<unknown, unknown>).entries()
  for (const [key, value] of left) {
    const entry = entries.next().value!
    if (!visit(key, entry[0]) || !visit(value, entry[1])) return false
  }
  return true
}

function setsEqual(left: Set<unknown>, right: object, visit: GraphVisit): boolean {
  if (!(right instanceof Set) || left.size !== right.size) return false
  const entries = (right as Set<unknown>).values()
  for (const value of left) if (!visit(value, entries.next().value)) return false
  return true
}

function propertiesEqual(left: object, right: object, visit: GraphVisit): boolean {
  const keys = Reflect.ownKeys(left)
  const rightKeys = Reflect.ownKeys(right)
  return (
    keys.length === rightKeys.length &&
    keys.every(
      (key, index) =>
        key === rightKeys[index] && visit(Reflect.get(left, key), Reflect.get(right, key)),
    )
  )
}

export interface GraphNode {
  [key: string]: unknown
  count: number
}
export type Special = ArrayBuffer | DataView | Date | Uint8Array

export function mixedGraph(random: ReturnType<typeof randomSource>, datesOnly: boolean) {
  const objects: GraphNode[] = Array.from({ length: 6 }, () => ({ count: 0 }))
  const buffer = new ArrayBuffer(4)
  const specials: Special[] = datesOnly
    ? [new Date(1), new Date(2), new Date(3), new Date(4), new Date(5)]
    : [new Date(1), new Date(2), buffer, new Uint8Array(buffer), new DataView(buffer)]
  const map = new Map<object, object>()
  const set = new Set<object>()
  const array: object[] = []
  const values: object[] = [...objects, ...specials, map, set, array]
  for (const object of objects)
    for (let index = 0; index < 2; index += 1)
      object[`k${index}`] = values[random.next(values.length)]
  for (let index = 0; index < 2; index += 1) {
    map.set(values[random.next(values.length)], values[random.next(values.length)])
    set.add(values[random.next(values.length)])
    array.push(values[random.next(values.length)])
  }
  return { objects, specials, values }
}

export function graphResult(root: object, raw: object, special: object): Record<string, object> {
  // Preserve the original fuzzer's root/raw/special traversal order.
  return Object.fromEntries([
    ['root', root],
    ['raw', raw],
    ['special', special],
  ])
}

export function mutateSpecial(value: Special): void {
  if (value instanceof Date) value.setTime(9)
  else new Uint8Array(value instanceof ArrayBuffer ? value : value.buffer)[0] = 9
}

export interface SequenceNode {
  n: number
  next?: SequenceNode
}

export interface SequenceFixture {
  buffer: ArrayBuffer
  data: DataView
  date: Date
  list: Array<SequenceNode | undefined>
  map: Map<SequenceNode, SequenceNode>
  nodes: SequenceNode[]
  set: Set<SequenceNode>
  view: Uint16Array
}

export function sequenceFixture(): SequenceFixture {
  const nodes: SequenceNode[] = Array.from({ length: 4 }, (_, index) => ({ n: index }))
  for (let index = 0; index < 4; index += 1) nodes[index].next = nodes[(index + 1) % 4]
  const buffer = new ArrayBuffer(16)
  const list = new Array<SequenceNode | undefined>(4)
  list[0] = nodes[0]
  list[2] = nodes[1]
  list[3] = nodes[0]
  // Insertion order affects finalization; keep the original fixture order.
  return Object.fromEntries<unknown>([
    ['nodes', nodes],
    ['list', list],
    ['map', new Map([[nodes[0], nodes[1]]])],
    ['set', new Set([nodes[0]])],
    ['date', new Date(0)],
    ['buffer', buffer],
    ['view', new Uint16Array(buffer, 2, 3)],
    ['data', new DataView(buffer, 1, 8)],
  ]) as unknown as SequenceFixture
}

type SequenceOperation = (
  draft: SequenceFixture,
  node: SequenceNode,
  a: number,
  b: number,
  held: SequenceNode,
) => void

// Indexed by operation code. `node` is read from the draft before every operation.
const sequenceOperations: Partial<Record<number, SequenceOperation>> = {
  0: (draft, node) => {
    draft.list.push(node)
  },
  1: (draft, node) => {
    draft.list.unshift(node)
  },
  10: (_draft, node, _a, b) => {
    node.n = b
  },
  11: (draft, node, _a, b) => {
    draft.map.set(node, draft.nodes[b % 4])
  },
  12: (draft, node) => {
    draft.map.delete(node)
  },
  13: (draft, node) => {
    draft.set.add(node)
  },
  14: (draft, node) => {
    draft.set.delete(node)
  },
  15: (draft, node) => {
    draft.map.get(node)
  },
  16: (draft, _node, _a, b) => {
    draft.date.setTime(b)
  },
  17: (draft, _node, a, b) => {
    draft.view[a % 3] = b
  },
  18: (draft, _node, a, b) => {
    draft.data.setUint8(a % 8, b)
  },
  19: (draft, node, a, b) => {
    draft.list.fill(node, a % 6, b % 7)
  },
  2: (draft, node, a, b) => {
    draft.list.splice(a % 6, b % 3, node)
  },
  20: (_draft, _node, _a, b, held) => {
    held.n = b
  },
  21: (draft) => {
    draft.map.clear()
  },
  22: (draft) => {
    draft.set.clear()
  },
  23: (draft) => {
    draft.list.sort((left, right) => left!.n - right!.n)
  },
  3: (draft) => {
    draft.list.reverse()
  },
  4: (draft, _node, a, b) => {
    draft.list.copyWithin(a % 6, b % 6)
  },
  5: (draft, _node, a) => {
    draft.list.length = a % 7
  },
  6: (draft, _node, a) => {
    assert.isTrue(Reflect.deleteProperty(draft.list, String(a % 7)))
  },
  7: (draft, node, a) => {
    draft.list[a % 7] = node
  },
  8: (draft) => {
    draft.list.pop()
  },
  9: (draft) => {
    draft.list.shift()
  },
}

export function runSequence(draft: ReturnType<typeof sequenceFixture>, operations: number[][]) {
  const held = draft.list[0]!
  for (const [operation, a, b] of operations) {
    const node = draft.nodes[a % 4]
    const apply = sequenceOperations[operation]
    if (apply === undefined) throw new Error(`Unknown sequence operation ${operation}`)
    apply(draft, node, a, b, held)
  }
  return draft
}

export function keyFixture() {
  const raw = [{ n: 0 }, { n: 1 }]
  const root = reactive({
    keys: raw,
    map: new Map<{ n: number }, { n: number } | undefined>([
      [raw[0], { n: 2 }],
      [raw[1], { n: 3 }],
    ]),
  })
  return { raw, root }
}

type KeyRoot = ReturnType<typeof keyFixture>['root']

type KeyOperation = (draft: KeyRoot, key: { n: number }, n: number, trace: unknown[]) => void

// Indexed by operation code. The key is resolved before every operation.
const keyOperations: Partial<Record<number, KeyOperation>> = {
  0: (draft, key, _n, trace) => {
    trace.push(draft.map.get(key)?.n)
  },
  1: (draft, key, _n, trace) => {
    trace.push(draft.map.has(key))
  },
  2: (draft, key, n) => {
    draft.map.set(key, { n })
  },
  3: (draft, key, _n, trace) => {
    trace.push(draft.map.delete(key))
  },
  4: (draft) => {
    draft.map.clear()
  },
  5: (draft, key, n) => {
    const value = draft.map.get(key)
    if (value !== undefined) value.n = n
  },
  6: (draft, key) => {
    draft.map.set(key, draft.map.get(key))
  },
}

// Form 0 uses the raw key, form 1 its Vue wrapper and form 2 the draft's own key element.
function operationKey(draft: KeyRoot, raw: Array<{ n: number }>, index: number, form: number) {
  return form === 0 ? raw[index] : form === 1 ? reactive(raw[index]) : draft.keys[index]
}

export function runKeySequence(
  draft: ReturnType<typeof keyFixture>['root'],
  raw: Array<{ n: number }>,
  operations: number[][],
) {
  const trace: unknown[] = []
  for (const [operation, index, form, n] of operations) {
    const key = operationKey(draft, raw, index, form)
    const apply = keyOperations[operation]
    if (apply === undefined) throw new Error(`Unknown key operation ${operation}`)
    apply(draft, key, n, trace)
    trace.push(draft.map.size)
  }
  return trace
}

export function operationOutcome(run: () => unknown): unknown[] {
  try {
    return ['return', run()]
  } catch (error) {
    if (!(error instanceof Error)) throw error
    return ['throw', error.name]
  }
}

export function physicalCopy(value: object): object {
  const copy: object = Array.isArray(value)
    ? new Array<unknown>(value.length)
    : (Object.create(Object.getPrototypeOf(value) as object | null) as object)
  Object.defineProperties(copy, Object.getOwnPropertyDescriptors(value))
  return copy
}

export function observedDescriptors(value: object): unknown[][] {
  return Reflect.ownKeys(value).map((key) => {
    const descriptor = Object.getOwnPropertyDescriptor(value, key)!
    // Draft arrays expose writable length on their empty proxy target. Actual
    // readonly semantics are compared separately through operation outcomes.
    return [
      key,
      'value' in descriptor ? (Reflect.get(value, key) as unknown) : 'accessor',
      Array.isArray(value) && key === 'length' ? true : descriptor.writable,
      descriptor.enumerable,
    ]
  })
}

export function keySequences(keys: PropertyKey[]): PropertyKey[][] {
  return [
    [],
    ...keys.flatMap((key, index) =>
      keySequences(keys.filter((_, position) => position !== index)).map((tail) => [key, ...tail]),
    ),
  ]
}

export function orderedObject(keys: PropertyKey[], fixed = 0, extensible = true): object {
  const value = Object.create(null) as object
  keys.forEach((key, index) =>
    Object.defineProperty(value, key, {
      configurable: (fixed & (1 << index)) === 0,
      enumerable: true,
      value: 0,
      writable: true,
    }),
  )
  if (!extensible) Object.preventExtensions(value)
  return value
}

export interface ReuseGraphNode {
  edges: Map<string, ReuseGraphNode>
  mark: number
}

export interface TinyNode {
  [key: string]: unknown
  value: number
}

export interface AttributeFlags {
  configurable: boolean
  enumerable: boolean
  writable: boolean
}

// All eight data-property attribute combinations, in configurable/enumerable/writable order.
export function attributeConfigurations(): AttributeFlags[] {
  const configurations: AttributeFlags[] = []
  for (const configurable of [false, true])
    for (const enumerable of [false, true])
      for (const writable of [false, true])
        configurations.push({ configurable, enumerable, writable })
  return configurations
}

// Three-node graphs encode the edge from -> to as bit 3 * from + to.
export function hasEdge(graph: number, from: number, to: number): boolean {
  return (graph & (1 << (3 * from + to))) !== 0
}

// Independently enumerate subsets: an unchanged retained node needs every
// outgoing node retained too. The union of valid subsets is itself valid.
export function greatestRetainedSubset(graph: number, changed: number): number {
  let greatest = 0
  for (let subset = 0; subset < 8; subset += 1) {
    if ((subset & changed) !== 0) continue
    if (isRetainable(graph, subset)) greatest |= subset
  }
  return greatest
}

function isRetainable(graph: number, subset: number): boolean {
  for (let from = 0; from < 3; from += 1)
    if ((subset & (1 << from)) !== 0)
      for (let to = 0; to < 3; to += 1)
        if (hasEdge(graph, from, to) && (subset & (1 << to)) === 0) return false
  return true
}

// One file keeps these bounded suites sequential instead of running several large
// graph workloads concurrently. Longer timeouts allow for coverage instrumentation.
