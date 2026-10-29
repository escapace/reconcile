// Native differential for `produce` and `reconcile`. Everything here is ordinary JavaScript and
// independent of the library and of the Lean models: a seeded graph generator, a
// descriptor-preserving copier, native recipes replayed on plain copies, and an ordered graph
// comparison. The README rules that let a result differ from the native one are the policies;
// every other difference is a failure.
/* eslint-disable baseline-js/use-baseline -- resizable buffers, on engines that have them */

/* --------------------------------------------------------------------------- random source */

/** mulberry32: small, deterministic per seed, and good in its low bits. */
export class Random {
  private state: number
  constructor(seed: number) {
    this.state = seed >>> 0
  }
  chance(probability: number): boolean {
    return this.next() < probability
  }
  int(bound: number): number {
    return Math.floor(this.next() * bound)
  }
  next(): number {
    this.state = (this.state + 0x6d_2b_79_f5) >>> 0
    let t = this.state
    t = Math.imul(t ^ (t >>> 15), t | 1)
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61)
    return ((t ^ (t >>> 14)) >>> 0) / 4_294_967_296
  }
  pick<T>(items: readonly T[]): T {
    return items[this.int(items.length)]
  }
  shuffle<T>(items: readonly T[]): T[] {
    const result = [...items]
    for (let index = result.length - 1; index > 0; index -= 1) {
      const other = this.int(index + 1)
      const held = result[index]
      result[index] = result[other]
      result[other] = held
    }
    return result
  }
}

/* ---------------------------------------------------------------------------------- values */

const SYMBOL_A = Symbol('a')
const SYMBOL_B = Symbol('b')
const SYMBOL_VALUE = Symbol('value')

/** Values every function keeps by reference (README: Objects kept by reference). */
const ATOMS: readonly unknown[] = [
  function atom(): number {
    return 0
  },
  /atom/g,
]
const PRIMITIVES: readonly unknown[] = [
  0,
  1,
  2,
  -0,
  Number.NaN,
  'x',
  'y',
  '',
  true,
  false,
  null,
  undefined,
  10n,
  SYMBOL_VALUE,
]
const MAP_KEYS: readonly unknown[] = [0, 1, -0, 'k', 'm', true, null, undefined, 2n]
const KEYS: ReadonlyArray<string | symbol> = [
  'a',
  'b',
  'c',
  'd',
  '0',
  '1',
  '__proto__',
  SYMBOL_A,
  SYMBOL_B,
]
const ACCESSOR_KEYS: readonly string[] = ['a', 'b', 'c', 'd']

type Getter = (this: unknown) => unknown
type Setter = (this: unknown, value: unknown) => void

/** Getters without setters that return a primitive. */
const CONSTANT_GETTERS: readonly Getter[] = [1, 'g', undefined, null].map(
  (value) =>
    function constant(): unknown {
      return value
    },
)

/**
 * A getter and setter pair for `key` that store the value in the data property `_key`. A
 * throwing setter assigns, so it throws where strict-mode assignment does; the other one uses
 * `Reflect.set` and can fail to store its value without an error. `reconcile` propagates a
 * setter's error (README: Errors), so its graphs use setters that do not throw.
 */
function backedAccessor(key: string, throwing: boolean): { get: Getter; set: Setter } {
  const store = `_${key}`
  return {
    set: throwing
      ? function set(this: unknown, value: unknown): void {
          ;(this as Record<string, unknown>)[store] = value
        }
      : function set(this: unknown, value: unknown): void {
          Reflect.set(this as object, store, value)
        },
    get(this: unknown): unknown {
      return (this as Record<string, unknown>)[store]
    },
  }
}
const BACKED = new Map(
  ACCESSOR_KEYS.map((key) => [key, [backedAccessor(key, false), backedAccessor(key, true)]]),
)

/* ----------------------------------------------------------------------------------- kinds */

type Kind = 'atom' | 'primitive' | NodeKind
type NodeKind =
  | 'array'
  | 'buffer'
  | 'DataView'
  | 'date'
  | 'Int16Array'
  | 'map'
  | 'object'
  | 'set'
  | 'Uint8Array'

const CLASS_KINDS: ReadonlyArray<readonly [abstract new (...parameters: never[]) => object, Kind]> =
  [
    [Map, 'map'],
    [Set, 'set'],
    [Date, 'date'],
    [ArrayBuffer, 'buffer'],
    [Uint8Array, 'Uint8Array'],
    [Int16Array, 'Int16Array'],
    [DataView, 'DataView'],
  ]

function kindOf(value: unknown): Kind {
  if (typeof value === 'function' || value instanceof RegExp) return 'atom'
  if (typeof value !== 'object' || value === null) return 'primitive'
  if (Array.isArray(value)) return 'array'
  const match = CLASS_KINDS.find(([constructor]) => value instanceof constructor)
  return match === undefined ? 'object' : match[1]
}

const isView = (kind: Kind): boolean =>
  kind === 'DataView' || kind === 'Int16Array' || kind === 'Uint8Array'

/** Whether a value is an object the functions copy or update, not a primitive or an atom. */
const isNode = (value: unknown): value is object => {
  const kind = kindOf(value)
  return kind !== 'primitive' && kind !== 'atom'
}

/** Whether a node is a typed array over a resizable buffer. */
const overResizable = (node: object): boolean =>
  ArrayBuffer.isView(node) && !(node instanceof DataView) && (node.buffer as ArrayBuffer).resizable

/** Whether this runtime refuses to make a typed array over a resizable buffer non-extensible, as
 * ECMAScript 2025 requires; Node.js 22 predates the rule and makes one non-extensible. */
const RESIZABLE_VIEWS_UNSEALABLE = (() => {
  try {
    Object.preventExtensions(new Uint8Array(new ArrayBuffer(1, { maxByteLength: 2 })))
    return false
  } catch {
    return true
  }
})()

/* ----------------------------------------------------------------------------------- paths */

type Path = readonly Step[]
type Step =
  | { index: number; kind: 'mapKey' }
  | { index: number; kind: 'mapValue' }
  | { index: number; kind: 'setMember' }
  | { key: PropertyKey; kind: 'key' }
  | { kind: 'buffer' }

const isIndex = (key: PropertyKey): key is string =>
  typeof key === 'string' && key !== '4294967295' && String(Number(key) >>> 0) === key

const keyStep = (node: object, key: PropertyKey): Step => ({
  key: Array.isArray(node) && isIndex(key) ? Number(key) : key,
  kind: 'key',
})

function formatStep(step: Step): string {
  if (step.kind === 'buffer') return '.buffer'
  if (step.kind !== 'key') return `.${step.kind}(${step.index})`
  if (typeof step.key === 'string') return `.${step.key}`
  return `[${String(step.key)}]`
}

const formatPath = (path: Path): string => `root${path.map((step) => formatStep(step)).join('')}`

function nth(iterator: Iterator<unknown>, index: number): unknown {
  let result = iterator.next()
  for (let count = 0; count < index; count += 1) result = iterator.next()
  return result.value
}

const STEP_READS: {
  [K in Step['kind']]: (value: unknown, step: Extract<Step, { kind: K }>) => unknown
} = {
  buffer: (value) => (value as ArrayBufferView).buffer,
  key: (value, step) => (value as Record<PropertyKey, unknown>)[step.key],
  mapKey: (value, step) => nth((value as Map<unknown, unknown>).keys(), step.index),
  mapValue: (value, step) => nth((value as Map<unknown, unknown>).values(), step.index),
  setMember: (value, step) => nth((value as Set<unknown>).values(), step.index),
}

/** Follows `path` with ordinary reads, so on a draft it reads drafts. */
function resolvePath(root: unknown, path: Path): unknown {
  let value = root
  for (const step of path)
    value = (STEP_READS[step.kind] as (value: unknown, step: Step) => unknown)(value, step)
  return value
}

/* ---------------------------------------------------------------------------------- facets */

type ChildVisit = (child: unknown, step: Step) => void
type Encode = (value: unknown) => string
type Visit = (left: unknown, right: unknown, path: string) => string | undefined

/** What the copier, the traversal, the state record, the comparison and the description need to
 * know about one kind of node. */
interface Facet {
  /** Visits every value the node holds: data property values (not getters), entries, buffers. */
  children: (node: object, visit: ChildVisit) => void
  /** Compares the contents of two paired nodes; `visit` pairs and compares their children. */
  compare: (
    left: object,
    right: object,
    path: string,
    visit: Visit,
    policy: ComparePolicy,
  ) => string | undefined
  /** Copies a node, registering the copy before copying its children. */
  copy: (
    node: object,
    copy: (value: unknown) => unknown,
    register: (target: object) => void,
  ) => object
  describe: (node: object, id: Encode) => string
  /** The node's own state, with child nodes encoded by identity. */
  state: (node: object, encode: Encode) => string[]
}

const flags = (descriptor: PropertyDescriptor): string =>
  ['writable', 'enumerable', 'configurable']
    .map((name) => (descriptor[name as keyof PropertyDescriptor] === true ? name[0] : '-'))
    .join('')

const descriptorOf = (node: object, key: PropertyKey): PropertyDescriptor =>
  Reflect.getOwnPropertyDescriptor(node, key)!

/** The value a property holds: its data value or what its getter returns. */
const valueOf = (node: object, descriptor: PropertyDescriptor): unknown =>
  'value' in descriptor ? descriptor.value : descriptor.get?.call(node)

function compareProperties(
  left: object,
  right: object,
  path: string,
  visit: Visit,
  policy: ComparePolicy,
): string | undefined {
  const keys = Reflect.ownKeys(left)
  const others = Reflect.ownKeys(right)
  if (keys.length !== others.length || keys.some((key, index) => key !== others[index]))
    return `${path}: keys [${keys.map(String).join(', ')}] differ from [${others.map(String).join(', ')}]`
  const kind = kindOf(left)
  for (const key of keys) {
    const expected = descriptorOf(left, key)
    const actual = descriptorOf(right, key)
    const at = `${path}${formatStep(keyStep(left, key))}`
    const attributes = policy.property(left, right, key, expected, actual, kind)
    if (attributes !== undefined) return `${at}: ${attributes}`
    const failure = visit(valueOf(left, expected), valueOf(right, actual), at)
    if (failure !== undefined) return failure
  }
  return undefined
}

function copyProperties(node: object, target: object, copy: (value: unknown) => unknown): void {
  for (const key of Reflect.ownKeys(node)) {
    if (Array.isArray(target) && key === 'length') continue
    const descriptor = descriptorOf(node, key)
    Object.defineProperty(
      target,
      key,
      'value' in descriptor ? { ...descriptor, value: copy(descriptor.value) } : descriptor,
    )
  }
}

const objectFacet: Facet = {
  compare: compareProperties,
  children(node, visit) {
    for (const key of Reflect.ownKeys(node)) {
      const descriptor = descriptorOf(node, key)
      if ('value' in descriptor) visit(descriptor.value, keyStep(node, key))
    }
  },
  copy(node, copy, register) {
    const target = Object.create(Object.getPrototypeOf(node) as object | null) as object
    register(target)
    copyProperties(node, target, copy)
    return target
  },
  describe: (node, id) =>
    Reflect.ownKeys(node)
      .map((key) => {
        const descriptor = descriptorOf(node, key)
        const shown = 'value' in descriptor ? id(descriptor.value) : 'accessor'
        return `${String(key)}: ${shown} ${flags(descriptor)}`
      })
      .join(', '),
  state: (node, encode) =>
    Reflect.ownKeys(node).map((key) => {
      const descriptor = descriptorOf(node, key)
      const held =
        'value' in descriptor
          ? `=${encode(descriptor.value)}`
          : // eslint-disable-next-line typescript/unbound-method -- encoded by identity, not called
            `${encode(descriptor.get)}${encode(descriptor.set)}`
      return `${encode(key)}${flags(descriptor)}${held}`
    }),
}

const arrayFacet: Facet = {
  ...objectFacet,
  copy(node, copy, register) {
    const target: unknown[] = []
    register(target)
    target.length = (node as unknown[]).length
    copyProperties(node, target, copy)
    if (descriptorOf(node, 'length').writable !== true)
      Object.defineProperty(target, 'length', { writable: false })
    return target
  },
}

/** Compares two lists of entries part by part; each part is labelled for the path. */
function compareEntries(
  left: unknown[][],
  right: unknown[][],
  path: string,
  visit: Visit,
  labels: readonly string[],
): string | undefined {
  if (left.length !== right.length)
    return `${path}: size ${left.length} differs from ${right.length}`
  for (let index = 0; index < left.length; index += 1)
    for (let part = 0; part < labels.length; part += 1) {
      const failure = visit(
        left[index][part],
        right[index][part],
        `${path}.${labels[part]}(${index})`,
      )
      if (failure !== undefined) return failure
    }
  return undefined
}

const entriesOf = (node: object): Array<[unknown, unknown]> => [...(node as Map<unknown, unknown>)]
const membersOf = (node: object): unknown[] => [...(node as Set<unknown>)]

const mapFacet: Facet = {
  children(node, visit) {
    entriesOf(node).forEach(([key, value], index) => {
      visit(key, { index, kind: 'mapKey' })
      visit(value, { index, kind: 'mapValue' })
    })
  },
  compare: (left, right, path, visit) =>
    compareEntries(entriesOf(left), entriesOf(right), path, visit, ['mapKey', 'mapValue']),
  copy(node, copy, register) {
    const target = new Map<unknown, unknown>()
    register(target)
    for (const [key, value] of entriesOf(node)) target.set(copy(key), copy(value))
    return target
  },
  describe: (node, id) =>
    entriesOf(node)
      .map(([key, value]) => `${id(key)} => ${id(value)}`)
      .join(', '),
  state: (node, encode) => entriesOf(node).flatMap(([key, value]) => [encode(key), encode(value)]),
}

const setFacet: Facet = {
  children(node, visit) {
    membersOf(node).forEach((member, index) => {
      visit(member, { index, kind: 'setMember' })
    })
  },
  compare: (left, right, path, visit) =>
    compareEntries(
      membersOf(left).map((member) => [member]),
      membersOf(right).map((member) => [member]),
      path,
      visit,
      ['setMember'],
    ),
  copy(node, copy, register) {
    const target = new Set<unknown>()
    register(target)
    for (const member of membersOf(node)) target.add(copy(member))
    return target
  },
  describe: (node, id) =>
    membersOf(node)
      .map((member) => id(member))
      .join(', '),
  state: (node, encode) => membersOf(node).map((member) => encode(member)),
}

/** A facet for a node without children, whose contents one string states. */
function leafFacet(text: (node: object) => string, copy: (node: object) => object): Facet {
  return {
    copy,
    describe: text,
    children: () => undefined,
    compare: (left, right, path) =>
      text(left) === text(right) ? undefined : `${path}: ${text(left)} differs from ${text(right)}`,
    state: (node) => [text(node)],
  }
}

const dateFacet = leafFacet(
  (node) => `time ${(node as Date).getTime()}`,
  (node) => new Date((node as Date).getTime()),
)

/** A buffer's bytes, and its maximum when it is resizable. */
function bufferText(node: object): string {
  const buffer = node as ArrayBuffer
  const maximum = buffer.resizable ? ` max ${buffer.maxByteLength}` : ''
  return `bytes [${new Uint8Array(buffer).join()}]${maximum}`
}

const bufferFacet = leafFacet(bufferText, (node) => {
  const buffer = node as ArrayBuffer
  if (!buffer.resizable) return buffer.slice(0)
  const copy = new ArrayBuffer(buffer.byteLength, { maxByteLength: buffer.maxByteLength })
  new Uint8Array(copy).set(new Uint8Array(buffer))
  return copy
})

type ViewConstructor = new (buffer: ArrayBuffer, offset: number, length: number) => object
const viewOf = (node: object): ArrayBufferView => node as ArrayBufferView
const geometry = (view: ArrayBufferView): string => `@${view.byteOffset}+${view.byteLength}`

/** Views have a fixed length; the generator makes no length-tracking views. */
const viewFacet: Facet = {
  children: (node, visit) => {
    visit(viewOf(node).buffer, { kind: 'buffer' })
  },
  compare(left, right, path, visit) {
    const [a, b] = [viewOf(left), viewOf(right)]
    if (geometry(a) !== geometry(b))
      return `${path}: view ${geometry(a)} differs from ${geometry(b)}`
    return visit(a.buffer, b.buffer, `${path}.buffer`)
  },
  copy(node, copy) {
    const view = viewOf(node)
    const size = view instanceof Int16Array ? 2 : 1
    return new (view.constructor as ViewConstructor)(
      copy(view.buffer) as ArrayBuffer,
      view.byteOffset,
      view.byteLength / size,
    )
  },
  describe: (node, id) => `${id(viewOf(node).buffer)} ${geometry(viewOf(node))}`,
  state: (node, encode) => [encode(viewOf(node).buffer), geometry(viewOf(node))],
}

const FACETS: Readonly<Record<NodeKind, Facet>> = {
  array: arrayFacet,
  buffer: bufferFacet,
  DataView: viewFacet,
  date: dateFacet,
  Int16Array: viewFacet,
  map: mapFacet,
  object: objectFacet,
  set: setFacet,
  Uint8Array: viewFacet,
}

const facetOf = (node: object): Facet => FACETS[kindOf(node) as NodeKind]

/* ------------------------------------------------------------------------- copy, traversal */

/**
 * Copies a graph with the same keys in order, descriptors, prototypes, extensibility, holes,
 * entry order, times, bytes, view geometry, sharing and cycles. Atoms and accessor functions
 * are shared. `copies` maps each source node to its copy.
 */
function deepCopy<T>(value: T, copies = new Map<object, object>()): T {
  const copy = (source: unknown): unknown => {
    if (!isNode(source)) return source
    const existing = copies.get(source)
    if (existing !== undefined) return existing
    const target = facetOf(source).copy(source, copy, (early) => copies.set(source, early))
    copies.set(source, target)
    if (!Object.isExtensible(source)) Object.preventExtensions(target)
    return target
  }
  return copy(value) as T
}

/** Every node reachable from `root`, in breadth-first order. */
function reachable(root: unknown): object[] {
  const seen = new Set<object>()
  const order: object[] = []
  const add = (value: unknown): void => {
    if (isNode(value) && !seen.has(value)) {
      seen.add(value)
      order.push(value)
    }
  }
  add(root)
  for (const node of order) facetOf(node).children(node, add)
  return order
}

interface Located {
  path: Path
  value: object
}

/**
 * The nodes reachable from `root` without passing through a `Map` key, each with its first path,
 * and every node reachable from a `Map` key. A produce recipe reads `Map` keys as they are, not as
 * drafts (README: `produce` limitations), so it never changes a node reachable from one.
 */
function survey(root: unknown): { keyed: Set<object>; located: Located[] } {
  const located: Located[] = [{ path: [], value: root as object }]
  const seen = new Set<object>([root as object])
  for (const entry of located)
    facetOf(entry.value).children(entry.value, (child, step) => {
      if (step.kind === 'mapKey' || !isNode(child) || seen.has(child)) return
      seen.add(child)
      located.push({ path: [...entry.path, step], value: child })
    })
  const keyed = new Set<object>()
  for (const node of reachable(root))
    if (node instanceof Map)
      for (const key of node.keys()) for (const inner of reachable(key)) keyed.add(inner)
  return { keyed, located }
}

/* ------------------------------------------------------------------------------ generation */

type ShapeKind = 'nullObject' | NodeKind

const NODE_KINDS: readonly ShapeKind[] = [
  'object',
  'object',
  'object',
  'nullObject',
  'array',
  'array',
  'map',
  'set',
  'date',
  'buffer',
  'Uint8Array',
  'Int16Array',
  'DataView',
]
const CONTAINER_KINDS: readonly ShapeKind[] = [
  'object',
  'object',
  'nullObject',
  'array',
  'map',
  'set',
]
const KEY_OBJECT_KINDS: readonly ShapeKind[] = ['object', 'nullObject', 'array']

interface GraphOptions {
  /** Getters and setters on objects below the root. */
  accessors: boolean
  /** Non-default property attributes and integrity levels. */
  attributes: boolean
  /** The largest number of nodes, before a buffer added for views. */
  nodes: number
  /** The root takes no accessor, no read-only non-configurable property and no integrity
   * level, so that `reconcile` can always update it. */
  plainRoot: boolean
  rootKinds: readonly ShapeKind[]
  /** Setters that throw where strict-mode assignment throws, instead of failing silently. */
  throwingSetters: boolean
}

/** The state of one graph under construction. */
interface Builder {
  keyObjects: object[]
  options: GraphOptions
  random: Random
  value: () => unknown
}

/** Builds a graph of up to `options.nodes` nodes, every one reachable from the root, with shared
 * references and cycles. */
function generateGraph(random: Random, options: GraphOptions): object {
  const kinds: ShapeKind[] = [random.pick(options.rootKinds)]
  // Only a container root can hold other nodes; a view root adds its buffer below.
  const count = CONTAINER_KINDS.includes(kinds[0]) ? 1 + random.int(options.nodes) : 1
  for (let index = 1; index < count; index += 1) kinds.push(random.pick(NODE_KINDS))
  if (kinds.some((kind) => isView(kind as Kind)) && !kinds.includes('buffer')) kinds.push('buffer')
  const nodes = kinds.map((kind) => createShell(random, kind))
  const buffers = nodes.filter((node) => node instanceof ArrayBuffer)
  kinds.forEach((kind, index) => {
    if (isView(kind as Kind)) nodes[index] = createView(random, kind, random.pick(buffers))
  })
  const builder: Builder = {
    keyObjects: nodes.filter(
      (_node, index) => index > 0 && KEY_OBJECT_KINDS.includes(kinds[index]),
    ),
    options,
    random,
    value: () => {
      if (random.chance(0.45)) return random.pick(nodes)
      return random.chance(0.1) ? random.pick(ATOMS) : random.pick(PRIMITIVES)
    },
  }
  nodes.forEach((node, index) => {
    fillNode(builder, node, index === 0 && options.plainRoot)
  })
  attachUnreachable(random, nodes)
  nodes.forEach((node, index) => {
    restrictNode(builder, node, index === 0)
  })
  return nodes[0]
}

function createShell(random: Random, kind: ShapeKind): object {
  if (kind === 'array') return []
  if (kind === 'date') return new Date(random.int(10) * 1000)
  if (kind === 'map') return new Map()
  if (kind === 'set') return new Set()
  if (kind === 'nullObject') return Object.create(null) as object
  if (kind !== 'buffer') return {}
  // A third are resizable; views over them have a fixed length.
  const length = random.int(9)
  const buffer = random.chance(0.3)
    ? new ArrayBuffer(length, { maxByteLength: length + random.int(5) })
    : new ArrayBuffer(length)
  const bytes = new Uint8Array(buffer)
  for (let index = 0; index < bytes.length; index += 1) bytes[index] = random.int(256)
  return buffer
}

function createView(random: Random, kind: ShapeKind, buffer: ArrayBuffer): object {
  const size = kind === 'Int16Array' ? 2 : 1
  const offset = size * random.int(Math.floor(buffer.byteLength / size) + 1)
  const elements = random.int(Math.floor((buffer.byteLength - offset) / size) + 1)
  if (kind === 'DataView') return new DataView(buffer, offset, elements)
  if (kind === 'Int16Array') return new Int16Array(buffer, offset, elements)
  return new Uint8Array(buffer, offset, elements)
}

function fillNode(builder: Builder, node: object, plain: boolean): void {
  const { random } = builder
  if (node instanceof Map)
    for (let entry = random.int(4); entry > 0; entry -= 1) {
      const objectKey = builder.keyObjects.length > 0 && random.chance(0.25)
      node.set(random.pick(objectKey ? builder.keyObjects : MAP_KEYS), builder.value())
    }
  else if (node instanceof Set)
    for (let member = random.int(4); member > 0; member -= 1) node.add(builder.value())
  else if (Array.isArray(node)) fillArray(builder, node, plain)
  else if (kindOf(node) === 'object') fillObject(builder, node, plain)
}

function attributes(builder: Builder, plain: boolean): PropertyDescriptor {
  const { random } = builder
  if (!builder.options.attributes || random.chance(0.75))
    return { configurable: true, enumerable: true, writable: true }
  const writable = random.chance(0.5)
  // A plain root has no read-only non-configurable property.
  const configurable = random.chance(0.5) || (plain && !writable)
  return { configurable, enumerable: random.chance(0.6), writable }
}

function fillObject(builder: Builder, node: object, plain: boolean): void {
  const { options, random } = builder
  for (const key of random.shuffle(KEYS).slice(0, 1 + random.int(4))) {
    const accessor = options.accessors && !plain && ACCESSOR_KEYS.includes(key as string)
    if (accessor && random.chance(0.15)) defineAccessor(builder, node, key as string)
    else Object.defineProperty(node, key, { ...attributes(builder, plain), value: builder.value() })
  }
}

/** Defines a constant getter, or a getter and setter backed by the data property `_key`, whose
 * value is a primitive so that the getter never returns a draft. */
function defineAccessor(builder: Builder, node: object, key: string): void {
  const { random } = builder
  const shape = { configurable: random.chance(0.8), enumerable: random.chance(0.8) }
  if (random.chance(0.5)) {
    Object.defineProperty(node, key, { ...shape, get: random.pick(CONSTANT_GETTERS) })
    return
  }
  const pair = BACKED.get(key)![builder.options.throwingSetters ? 1 : 0]
  const store = { configurable: random.chance(0.8), enumerable: random.chance(0.5), writable: true }
  const storeFirst = random.chance(0.5)
  const define = (): void => {
    Object.defineProperty(node, `_${key}`, { ...store, value: random.pick(PRIMITIVES) })
  }
  if (storeFirst) define()
  Object.defineProperty(node, key, { ...shape, get: pair.get, set: pair.set })
  if (!storeFirst) define()
}

function fillArray(builder: Builder, node: unknown[], plain: boolean): void {
  const { random } = builder
  const length = random.int(6)
  for (let index = 0; index < length; index += 1)
    if (!random.chance(0.15)) node[index] = builder.value()
  node.length = length
  if (!builder.options.attributes || plain || length === 0 || !random.chance(0.1)) return
  const index = random.int(length)
  Object.defineProperty(node, index, {
    configurable: random.chance(0.5),
    enumerable: random.chance(0.7),
    value: node[index],
    writable: random.chance(0.5),
  })
}

/** Hangs every node that the root does not reach off a reachable container. */
function attachUnreachable(random: Random, nodes: object[]): void {
  for (;;) {
    const seen = reachable(nodes[0])
    const missing = nodes.findIndex((node) => !seen.includes(node))
    if (missing === -1) return
    const host = random.pick(seen.filter((node) => isContainer(node)))
    const node = nodes[missing]
    if (host instanceof Map) host.set(`r${missing}`, node)
    else if (host instanceof Set) host.add(node)
    else if (Array.isArray(host)) host.push(node)
    else Object.defineProperty(host, `z${missing}`, { ...PLAIN_DATA, value: node })
  }
}

const PLAIN_DATA = { configurable: true, enumerable: true, writable: true }

const isContainer = (node: object): boolean => {
  const kind = kindOf(node)
  return kind === 'object' || kind === 'array' || kind === 'map' || kind === 'set'
}

type Integrity = 'freeze' | 'preventExtensions' | 'seal'

function restrict(node: object, level: Integrity): void {
  if (level === 'freeze') Object.freeze(node)
  else if (level === 'seal') Object.seal(node)
  else Object.preventExtensions(node)
}

function restrictNode(builder: Builder, node: object, root: boolean): void {
  const { options, random } = builder
  if (!options.attributes || (root && options.plainRoot) || overResizable(node)) return
  if (!random.chance(root ? 0.08 : 0.18)) return
  const levels: readonly Integrity[] = ['preventExtensions', 'seal', 'freeze']
  restrict(node, ArrayBuffer.isView(node) ? 'preventExtensions' : random.pick(levels))
}

/* ------------------------------------------------------------------------------ operations */

type KeySpec = { index: number; kind: 'entry' } | { kind: 'value'; value: ValueSpec }
type ValueSpec =
  | { kind: 'fresh'; template: object }
  | { kind: 'literal'; value: unknown }
  | { kind: 'ref'; path: Path }

type Operation =
  | {
      attributes: PropertyDescriptor
      key: PropertyKey
      kind: 'define'
      target: Path
      value: ValueSpec
    }
  | { deleteCount: number; kind: 'splice'; start: number; target: Path; values: ValueSpec[] }
  | {
      index: number
      kind: 'bytes'
      target: Path
      value: number
      via: 'buffer' | 'element' | 'view'
    }
  | { key: KeySpec; kind: 'mapDelete' | 'setDelete'; target: Path }
  | { key: KeySpec; kind: 'mapSet'; target: Path; value: ValueSpec }
  | { key: PropertyKey; kind: 'delete'; target: Path }
  | { key: PropertyKey; kind: 'set'; target: Path; value: ValueSpec }
  | { kind: 'clear' | 'pop' | 'reverse' | 'shift'; target: Path }
  | { kind: 'integrity'; level: Integrity; target: Path }
  | { kind: 'length' | 'resize'; length: number; target: Path }
  | { kind: 'prototype'; prototype: 'null' | 'object'; target: Path }
  | { kind: 'push' | 'setAdd' | 'unshift'; target: Path; value: ValueSpec }
  | { kind: 'setTime'; target: Path; time: number }
type OperationOf<K extends Operation['kind']> = { kind: K } & Operation

/** A fresh value created while a recipe runs: its template and the copy of each template node. */
interface Created {
  copies: Map<object, object>
  template: object
}

type Target = Record<PropertyKey, unknown>

/** Turns the specifications of an operation into values, against one root. */
interface Materialize {
  key: (spec: KeySpec) => unknown
  value: (spec: ValueSpec) => unknown
}

const listOf = (target: Target): unknown[] => target as unknown as unknown[]
const collectionOf = (target: Target): Map<unknown, unknown> & Set<unknown> =>
  target as unknown as Map<unknown, unknown> & Set<unknown>

function writeByte(target: Target, operation: OperationOf<'bytes'>): void {
  if (operation.via === 'view')
    (target as unknown as DataView).setUint8(operation.index, operation.value)
  else if (operation.via === 'buffer')
    new Uint8Array(target as unknown as ArrayBuffer)[operation.index] = operation.value
  else listOf(target)[operation.index] = operation.value
}

/** Each operation in ordinary JavaScript, on a plain graph or a draft alike. */
const RUNNERS: {
  [K in Operation['kind']]: (target: Target, operation: OperationOf<K>, make: Materialize) => void
} = {
  bytes: (target, operation) => {
    writeByte(target, operation)
  },
  clear: (target) => {
    collectionOf(target).clear()
  },
  define: (target, operation, make) => {
    const value = make.value(operation.value)
    Object.defineProperty(target, operation.key, { ...operation.attributes, value })
  },
  delete: (target, operation) => {
    delete target[operation.key]
  },
  integrity: (target, operation) => {
    restrict(target, operation.level)
  },
  length: (target, operation) => {
    listOf(target).length = operation.length
  },
  mapDelete: (target, operation, make) => {
    collectionOf(target).delete(make.key(operation.key))
  },
  mapSet: (target, operation, make) => {
    const key = make.key(operation.key)
    collectionOf(target).set(key, make.value(operation.value))
  },
  pop: (target) => {
    listOf(target).pop()
  },
  prototype: (target, operation) => {
    Object.setPrototypeOf(target, operation.prototype === 'null' ? null : Object.prototype)
  },
  push: (target, operation, make) => {
    listOf(target).push(make.value(operation.value))
  },
  resize: (target, operation) => {
    ;(target as unknown as ArrayBuffer).resize(operation.length)
  },
  reverse: (target) => {
    listOf(target).reverse()
  },
  set: (target, operation, make) => {
    target[operation.key] = make.value(operation.value)
  },
  setAdd: (target, operation, make) => {
    collectionOf(target).add(make.value(operation.value))
  },
  setDelete: (target, operation, make) => {
    collectionOf(target).delete(make.key(operation.key))
  },
  setTime: (target, operation) => {
    ;(target as unknown as Date).setTime(operation.time)
  },
  shift: (target) => {
    listOf(target).shift()
  },
  splice: (target, operation, make) => {
    const values = operation.values.map((value) => make.value(value))
    listOf(target).splice(operation.start, operation.deleteCount, ...values)
  },
  unshift: (target, operation, make) => {
    listOf(target).unshift(make.value(operation.value))
  },
}

function materialize(root: unknown, spec: ValueSpec, created: Created[]): unknown {
  if (spec.kind === 'literal') return spec.value
  if (spec.kind === 'ref') return resolvePath(root, spec.path)
  const copies = new Map<object, object>()
  const value = deepCopy(spec.template, copies)
  created.push({ copies, template: spec.template })
  return value
}

/** Runs one operation on `root` and returns `ok` or the name of the error it threw. */
function applyOperation(root: unknown, operation: Operation, created: Created[]): string {
  try {
    const target = resolvePath(root, operation.target) as Target
    const make: Materialize = {
      key: (spec) => {
        if (spec.kind === 'value') return materialize(root, spec.value, created)
        const keys =
          target instanceof Map ? target.keys() : (target as unknown as Set<unknown>).values()
        return nth(keys, spec.index)
      },
      value: (spec) => materialize(root, spec, created),
    }
    const run = RUNNERS[operation.kind] as (
      target: Target,
      operation: Operation,
      make: Materialize,
    ) => void
    run(target, operation, make)
    return 'ok'
  } catch (error) {
    if (error instanceof Error) return error.name
    throw error
  }
}

/* -------------------------------------------------------------------------------- planning */

type PlanMode = 'next' | 'produce'
type PlanValue = (primitiveOnly?: boolean) => ValueSpec

const freshOptions = (options: GraphOptions, rootKinds = NODE_KINDS): GraphOptions => ({
  ...options,
  nodes: 2,
  plainRoot: false,
  rootKinds,
})

function planValue(
  random: Random,
  located: readonly Located[],
  options: GraphOptions,
  primitiveOnly: boolean,
): ValueSpec {
  const roll = random.next()
  if (primitiveOnly || roll < 0.45) return { kind: 'literal', value: random.pick(PRIMITIVES) }
  if (roll < 0.53) return { kind: 'literal', value: random.pick(ATOMS) }
  if (roll < 0.78) return { kind: 'ref', path: random.pick(located).path }
  return { kind: 'fresh', template: generateGraph(random, freshOptions(options)) }
}

/** Plans one operation on the plain graph `root`, or none when nothing can change. In `produce`
 * mode it never targets a node reachable from a `Map` key. */
function planOperation(
  random: Random,
  root: unknown,
  mode: PlanMode,
  options: GraphOptions,
): Operation | undefined {
  const { keyed, located } = survey(root)
  const targets = located.filter((entry) => mode === 'next' || !keyed.has(entry.value))
  if (targets.length === 0) return undefined
  // Favour non-extensible targets, whose refusals the draft must reproduce.
  const hardened = targets.filter((entry) => !Object.isExtensible(entry.value))
  const chosen = random.pick(hardened.length > 0 && random.chance(0.4) ? hardened : targets)
  const target = chosen.path
  const node = chosen.value
  const value: PlanValue = (primitiveOnly = false) =>
    planValue(random, located, options, primitiveOnly)
  const nextOnly = mode === 'next' && random.chance(0.12)
  const plan = nextOnly ? planNextOnly(random, target, node, value) : undefined
  if (plan !== undefined) return plan
  if (Array.isArray(node)) return planArray(random, target, node, value)
  if (node instanceof Map) return planMap(random, target, node, value, options)
  if (node instanceof Set) return planSet(random, target, node, value)
  if (node instanceof Date) return { kind: 'setTime', target, time: random.int(12) * 1000 }
  if (kindOf(node) === 'object') return planObject(random, target, node, value)
  if (node instanceof ArrayBuffer && node.resizable && random.chance(0.4))
    return planResize(random, target, node, root, mode)
  return planBytes(random, target, node)
}

function planObject(random: Random, target: Path, node: object, value: PlanValue): Operation {
  const own = Reflect.ownKeys(node)
  const roll = random.next()
  if (own.length > 0 && roll < 0.2) return { key: random.pick(own), kind: 'delete', target }
  const existing = own.length > 0 && roll < 0.65 ? random.pick(own) : undefined
  const descriptor = existing === undefined ? undefined : descriptorOf(node, existing)
  if (descriptor !== undefined && 'value' in descriptor)
    return { key: existing!, kind: 'set', target, value: value() }
  // An assignment to a getter without a setter has no README rule for drafts.
  if (descriptor?.set !== undefined)
    return { key: existing!, kind: 'set', target, value: value(true) }
  return planAbsentKey(random, target, node, own, value)
}

function planAbsentKey(
  random: Random,
  target: Path,
  node: object,
  own: readonly PropertyKey[],
  value: PlanValue,
): Operation {
  const absent = KEYS.filter((key) => !own.includes(key))
  const key = random.pick(absent.length > 0 ? absent : KEYS)
  const descriptor = Reflect.getOwnPropertyDescriptor(node, key)
  // Assigning a `__proto__` key that the object lacks runs the setter on Object.prototype, which
  // a draft refuses (README: `produce` limitations, Assignment only).
  const inherited = key === '__proto__' && Object.getPrototypeOf(node) !== null
  const refused = descriptor === undefined ? inherited : !('value' in descriptor)
  return refused ? { key, kind: 'delete', target } : { key, kind: 'set', target, value: value() }
}

function planArray(random: Random, target: Path, node: unknown[], value: PlanValue): Operation {
  const length = node.length
  switch (random.int(10)) {
    case 0:
      return { kind: 'push', target, value: value() }
    case 1:
      return { kind: random.pick(['pop', 'shift', 'reverse'] as const), target }
    case 2:
      return { kind: 'unshift', target, value: value() }
    case 3: {
      const values = Array.from({ length: random.int(3) }, () => value())
      const start = random.int(length + 1)
      return { deleteCount: random.int(3), kind: 'splice', start, target, values }
    }
    case 4:
      return { kind: 'length', length: random.int(length + 3), target }
    case 5:
      return { key: random.int(length + 1), kind: 'delete', target }
    default:
      return { key: random.int(length + 2), kind: 'set', target, value: value() }
  }
}

function planBytes(random: Random, target: Path, node: object): Operation | undefined {
  const size = node instanceof ArrayBuffer ? node.byteLength : viewOf(node).byteLength
  if (size === 0) return undefined
  const byte = random.int(256)
  if (node instanceof ArrayBuffer)
    return { index: random.int(size), kind: 'bytes', target, value: byte, via: 'buffer' }
  if (node instanceof DataView)
    return { index: random.int(size), kind: 'bytes', target, value: byte, via: 'view' }
  const length = (node as Int16Array | Uint8Array).length
  const element = node instanceof Int16Array ? random.int(65_536) - 32_768 : byte
  return { index: random.int(length), kind: 'bytes', target, value: element, via: 'element' }
}

/**
 * Resizes a resizable buffer. A recipe only grows it: the README gives drafts a separate rule for
 * fixed-length views that a shrink leaves out of bounds (Dates and binary data). `next` can
 * shrink it down to the end of the furthest view over it.
 */
function planResize(
  random: Random,
  target: Path,
  node: ArrayBuffer,
  root: unknown,
  mode: PlanMode,
): Operation | undefined {
  const views = reachable(root).filter(
    (other) => ArrayBuffer.isView(other) && other.buffer === node,
  ) as ArrayBufferView[]
  const ends = views.map((view) => view.byteOffset + view.byteLength)
  const least = mode === 'next' ? Math.max(0, ...ends) : node.byteLength
  if (least >= node.maxByteLength) return undefined
  return { kind: 'resize', length: least + random.int(node.maxByteLength - least + 1), target }
}

function planMap(
  random: Random,
  target: Path,
  node: Map<unknown, unknown>,
  value: PlanValue,
  options: GraphOptions,
): Operation {
  const roll = random.next()
  const entry: KeySpec = { index: random.int(node.size), kind: 'entry' }
  if (node.size > 0 && roll < 0.35) return { key: entry, kind: 'mapSet', target, value: value() }
  if (node.size > 0 && roll < 0.55) return { key: entry, kind: 'mapDelete', target }
  if (roll < 0.6) return { kind: 'clear', target }
  const key: ValueSpec = random.chance(0.25)
    ? { kind: 'fresh', template: generateGraph(random, freshOptions(options, KEY_OBJECT_KINDS)) }
    : { kind: 'literal', value: random.pick(MAP_KEYS) }
  if (roll < 0.7) return { key: { kind: 'value', value: key }, kind: 'mapDelete', target }
  return { key: { kind: 'value', value: key }, kind: 'mapSet', target, value: value() }
}

function planSet(random: Random, target: Path, node: Set<unknown>, value: PlanValue): Operation {
  const roll = random.next()
  if (node.size > 0 && roll < 0.35)
    return { key: { index: random.int(node.size), kind: 'entry' }, kind: 'setDelete', target }
  if (roll < 0.4) return { kind: 'clear', target }
  if (roll >= 0.5) return { kind: 'setAdd', target, value: value() }
  const absent: ValueSpec = { kind: 'literal', value: random.pick(PRIMITIVES) }
  return { key: { kind: 'value', value: absent }, kind: 'setDelete', target }
}

/** Operations a recipe cannot run on a draft, applied only to build `next` for `reconcile`. */
function planNextOnly(
  random: Random,
  target: Path,
  node: object,
  value: PlanValue,
): Operation | undefined {
  const roll = random.next()
  const levels: readonly Integrity[] = ['freeze', 'preventExtensions', 'seal']
  const level = ArrayBuffer.isView(node) ? 'preventExtensions' : random.pick(levels)
  if (roll < 0.3) return { kind: 'integrity', level, target }
  if (kindOf(node) !== 'object') return undefined
  if (roll < 0.55)
    return { kind: 'prototype', prototype: random.pick(['null', 'object'] as const), target }
  const attributes = {
    configurable: random.chance(0.5),
    enumerable: random.chance(0.5),
    writable: random.chance(0.5),
  }
  return { attributes, key: random.pick(KEYS), kind: 'define', target, value: value() }
}

interface Recipe {
  created: Created[]
  operations: Operation[]
  outcomes: string[]
}

/** Plans and runs up to six operations, or eight for `next`, on the plain graph `root`; `record`
 * sees each value the recipe creates. */
function planRecipe(
  random: Random,
  root: unknown,
  mode: PlanMode,
  options: GraphOptions,
  record: (created: Created) => void = () => undefined,
): Recipe {
  const recipe: Recipe = { created: [], operations: [], outcomes: [] }
  for (let step = 1 + random.int(mode === 'next' ? 8 : 6); step > 0; step -= 1) {
    const operation = planOperation(random, root, mode, options)
    if (operation === undefined) break
    const count = recipe.created.length
    recipe.outcomes.push(applyOperation(root, operation, recipe.created))
    recipe.operations.push(operation)
    for (const created of recipe.created.slice(count)) record(created)
  }
  return recipe
}

/** Runs the operations of a recipe again on another root, such as a draft. */
function replayRecipe(root: unknown, operations: readonly Operation[]): Recipe {
  const created: Created[] = []
  const outcomes = operations.map((operation) => applyOperation(root, operation, created))
  return { created, operations: [...operations], outcomes }
}

/* ------------------------------------------------------------------------------ state record */

class Identity {
  private readonly ids = new Map<unknown, number>()
  /** Encodes a primitive by value and an object, function or symbol by identity. */
  readonly encode = (value: unknown): string => {
    if (typeof value === 'string') return JSON.stringify(value)
    if (typeof value === 'number' || typeof value === 'bigint' || typeof value === 'boolean')
      return `${typeof value}:${Object.is(value, -0) ? '-0' : String(value)}`
    if (value === undefined) return 'undefined'
    let id = this.ids.get(value)
    if (id === undefined) {
      id = this.ids.size
      this.ids.set(value, id)
    }
    return `#${id}`
  }
}

/** A node's own state: kind, extensibility, prototype and contents, with children by identity. */
const fingerprint = (node: object, encode: Encode): string =>
  [
    kindOf(node),
    String(Object.isExtensible(node)),
    encode(Object.getPrototypeOf(node)),
    ...facetOf(node).state(node, encode),
  ].join('|')

/**
 * Records the state of native nodes before a recipe changes them, and the object that `produce`
 * must return for each one whose subtree the recipe leaves unchanged.
 */
class Tracker {
  /** Native node to the object the result must hold when the node's subtree is unchanged. */
  readonly identity = new Map<object, object>()
  private readonly ids = new Identity()
  /** The objects of `current` and the values the recipe added; every other object is new. */
  readonly kept = new Set<object>()
  private readonly states = new Map<object, string>()

  /** The nodes reachable from `root` whose own state changed, or that reach one that did. A node
   * without a recorded state counts as changed. */
  changed(root: unknown): Set<object> {
    const parents = new Map<object, object[]>()
    const changed = new Set<object>()
    const pending: object[] = []
    for (const node of reachable(root)) {
      facetOf(node).children(node, (child) => {
        if (isNode(child)) parents.set(child, [...(parents.get(child) ?? []), node])
      })
      if (this.states.get(node) !== fingerprint(node, this.ids.encode)) pending.push(node)
    }
    for (const node of pending) {
      if (changed.has(node)) continue
      changed.add(node)
      pending.push(...(parents.get(node) ?? []))
    }
    return changed
  }

  pair(node: object, source: object): void {
    this.identity.set(node, source)
    this.kept.add(source)
  }

  record(node: object, source?: object): void {
    this.states.set(node, fingerprint(node, this.ids.encode))
    if (source !== undefined) this.pair(node, source)
  }
}

/* ------------------------------------------------------------------------------ comparison */

interface ComparePolicy {
  /** Checks a paired node's prototype and extensibility. */
  node: (expected: object, actual: object, kind: Kind) => string | undefined
  /** Checks the descriptors of a property that both nodes have. */
  property: (
    expected: object,
    actual: object,
    key: PropertyKey,
    expectedDescriptor: PropertyDescriptor,
    actualDescriptor: PropertyDescriptor,
    kind: Kind,
  ) => string | undefined
}

const FORMATS: Partial<Record<string, (value: unknown) => string>> = {
  bigint: (value) => `${value as bigint}n`,
  function: () => 'function',
  number: (value) => (Object.is(value, -0) ? '-0' : String(value)),
  object: (value) => (value === null ? 'null' : kindOf(value)),
  string: (value) => JSON.stringify(value),
}
const formatValue = (value: unknown): string => (FORMATS[typeof value] ?? String)(value)

/**
 * Compares two graphs in order and returns the first difference with its path, and the pairing
 * of expected to actual nodes. Both directions of the pairing are kept, so that splitting one
 * shared node and merging two distinct ones both fail.
 */
function compareGraphs(
  expected: unknown,
  actual: unknown,
  policy: ComparePolicy,
): { failure: string | undefined; images: Map<object, object> } {
  const images = new Map<object, object>()
  const owners = new Set<object>()
  const visit: Visit = (left, right, path) => {
    if (!isNode(left))
      return Object.is(left, right)
        ? undefined
        : `${path}: expected ${formatValue(left)}, got ${formatValue(right)}`
    const kind = kindOf(left)
    if (kindOf(right) !== kind) return `${path}: expected ${kind}, got ${formatValue(right)}`
    const node = right as object
    const image = images.get(left)
    if (image !== undefined)
      return image === node ? undefined : `${path}: a shared ${kind} is split in two`
    if (owners.has(node)) return `${path}: two distinct ${kind}s are merged`
    images.set(left, node)
    owners.add(node)
    const failure = policy.node(left, node, kind)
    if (failure !== undefined) return `${path}: ${failure}`
    return FACETS[kind as NodeKind].compare(left, node, path, visit, policy)
  }
  return { failure: visit(expected, actual, 'root'), images }
}

const describeDescriptor = (descriptor: PropertyDescriptor): string =>
  `${'value' in descriptor ? 'data' : 'accessor'} ${flags(descriptor)}`

function sameAttributes(expected: PropertyDescriptor, actual: PropertyDescriptor): boolean {
  const fields = ['value' in expected ? 'writable' : 'get', 'set', 'enumerable', 'configurable']
  return (
    'value' in expected === 'value' in actual &&
    fields.every(
      (field) =>
        expected[field as keyof PropertyDescriptor] === actual[field as keyof PropertyDescriptor],
    )
  )
}

function prototypeAndExtensibility(
  actual: object,
  prototype: unknown,
  extensible: boolean | undefined,
): string | undefined {
  if (Object.getPrototypeOf(actual) !== prototype) return 'prototype differs'
  if (extensible === undefined || Object.isExtensible(actual) === extensible) return undefined
  return `expected ${extensible ? 'an extensible' : 'a non-extensible'} object`
}

const attributeFailure = (expected: PropertyDescriptor, actual: PropertyDescriptor) =>
  sameAttributes(expected, actual)
    ? undefined
    : `expected ${describeDescriptor(expected)}, got ${describeDescriptor(actual)}`

/** Identical graphs: the same prototypes, extensibility and descriptors. */
const exactPolicy: ComparePolicy = {
  node: (expected, actual) =>
    prototypeAndExtensibility(
      actual,
      Object.getPrototypeOf(expected),
      Object.isExtensible(expected),
    ),
  property: (_expected, _actual, _key, expectedDescriptor, actualDescriptor) =>
    attributeFailure(expectedDescriptor, actualDescriptor),
}

/**
 * The README's rules for a `produce` result compared with native mutation. `kept` holds the
 * objects of `current` and the values the recipe added; any other object is new.
 *
 * - Supported values: a copy keeps its source's prototype.
 * - Properties and class instances, and the `produce` Remarks: a changed object keeps its
 *   extensibility and the attributes of its existing data properties, and properties the recipe
 *   adds are writable, enumerable and configurable, as native assignment makes them. The
 *   attribute rule excludes arrays: every element of an array that `produce` rebuilds is writable,
 *   enumerable and configurable (Limitations, Array element attributes are not copied).
 * - `produce` limitations, Changed dates, buffers and URLs are not extensible: a changed date,
 *   buffer or view is non-extensible, except a typed array over a resizable buffer in a runtime
 *   that cannot make it non-extensible.
 * - Properties and class instances: in a new object each getter is replaced by a data property
 *   that holds its value and has its enumerability.
 */
/** Why an element of a new array, or one added to an array, is not a writable, enumerable and
 * configurable data property, or undefined when it is; the README states nothing about `length`. */
const arrayProperty = (key: PropertyKey, actual: PropertyDescriptor): string | undefined =>
  key === 'length' || ('value' in actual && sameAttributes({ ...PLAIN_DATA, value: 0 }, actual))
    ? undefined
    : `an element of a new array is writable, enumerable and configurable, got ${describeDescriptor(actual)}`

function producePolicy(kept: ReadonlySet<object>): ComparePolicy {
  return {
    node(expected, actual, kind) {
      const copied = !kept.has(actual) && (kind === 'date' || kind === 'buffer' || isView(kind))
      const extensible = copied
        ? RESIZABLE_VIEWS_UNSEALABLE && overResizable(actual)
        : Object.isExtensible(expected)
      return prototypeAndExtensibility(actual, Object.getPrototypeOf(expected), extensible)
    },
    property(_expected, actual, key, expectedDescriptor, actualDescriptor, kind) {
      if (kind === 'array' && !kept.has(actual)) return arrayProperty(key, actualDescriptor)
      if (kept.has(actual) || 'value' in expectedDescriptor)
        return attributeFailure(expectedDescriptor, actualDescriptor)
      if (!('value' in actualDescriptor)) return 'expected a data property in a new object'
      if (actualDescriptor.enumerable === expectedDescriptor.enumerable) return undefined
      return 'a replaced getter keeps its enumerability'
    },
  }
}

interface OwnState {
  descriptors: Map<PropertyKey, PropertyDescriptor>
  extensible: boolean
  prototype: object | null
}

/** Records each node's prototype, extensibility and own descriptors before a call. */
function recordStates(root: unknown): Map<object, OwnState> {
  const states = new Map<object, OwnState>()
  for (const node of reachable(root)) {
    const properties = kindOf(node) === 'array' || kindOf(node) === 'object'
    const keys = properties ? Reflect.ownKeys(node) : []
    states.set(node, {
      descriptors: new Map(keys.map((key) => [key, descriptorOf(node, key)])),
      extensible: Object.isExtensible(node),
      prototype: Object.getPrototypeOf(node) as object | null,
    })
  }
  return states
}

/**
 * The README's rules for a `reconcile` result compared with `next`. `states` holds every object
 * of `current` as it was before the call; an object of the result that is not among them is new.
 *
 * - `reconcile` Remarks: a kept object keeps its prototype; a property it keeps has its own
 *   attributes, and an own getter or setter is kept; a property it adds is writable and
 *   configurable and takes the enumerability of the property in `next`.
 * - Supported values: a new copy keeps its source's prototype.
 * - Limitations, Array element attributes are not copied: an element added to an array, kept or
 *   new, is writable, enumerable and configurable, whatever its attributes in `next`.
 */
function reconcilePolicy(states: ReadonlyMap<object, OwnState>): ComparePolicy {
  return {
    node(expected, actual) {
      const state = states.get(actual)
      return state === undefined
        ? prototypeAndExtensibility(actual, Object.getPrototypeOf(expected), undefined)
        : prototypeAndExtensibility(actual, state.prototype, state.extensible)
    },
    property(_expected, actual, key, expectedDescriptor, actualDescriptor, kind) {
      const own = states.get(actual)?.descriptors.get(key)
      if (own !== undefined) return attributeFailure(own, actualDescriptor)
      if (kind === 'array') return arrayProperty(key, actualDescriptor)
      if (!('value' in actualDescriptor)) return 'expected an added data property'
      const added = { ...PLAIN_DATA, enumerable: expectedDescriptor.enumerable, value: 0 }
      if (sameAttributes(added, actualDescriptor)) return undefined
      return `an added property is writable and configurable with next's enumerability, got ${describeDescriptor(actualDescriptor)}`
    },
  }
}

/* ----------------------------------------------------------------------------- description */

function integrityOf(node: object): string {
  if (Object.isFrozen(node)) return ' frozen'
  if (Object.isSealed(node)) return ' sealed'
  return Object.isExtensible(node) ? '' : ' non-extensible'
}

/** A readable listing of a graph's nodes, for reproducing a failure. */
function describeGraph(root: unknown): string {
  const nodes = reachable(root)
  const id = (value: unknown): string =>
    isNode(value) ? `#${nodes.indexOf(value)}` : formatValue(value)
  return nodes
    .map((node, index) => {
      const prototype = Object.getPrototypeOf(node) === null ? ' null-prototype' : ''
      const contents = facetOf(node).describe(node, id)
      return `#${index} ${kindOf(node)}${prototype}${integrityOf(node)} { ${contents} }`
    })
    .join('\n')
}

function formatSpec(spec: ValueSpec): string {
  if (spec.kind === 'literal') return formatValue(spec.value)
  if (spec.kind === 'ref') return formatPath(spec.path)
  return `fresh(${describeGraph(spec.template).replaceAll('\n', '; ')})`
}

const formatKey = (key: PropertyKey): string => formatStep({ key, kind: 'key' })
const formatKeySpec = (key: KeySpec): string =>
  key.kind === 'entry' ? `entry ${key.index}` : formatSpec(key.value)

const FORMATTERS: {
  [K in Operation['kind']]: (operation: OperationOf<K>, target: string) => string
} = {
  bytes: (operation, target) =>
    `${target} ${operation.via}[${operation.index}] = ${operation.value}`,
  clear: (_operation, target) => `${target}.clear()`,
  define: (operation, target) =>
    `Object.defineProperty(${target}, ${String(operation.key)}, ${flags(operation.attributes)} ${formatSpec(operation.value)})`,
  delete: (operation, target) => `delete ${target}${formatKey(operation.key)}`,
  integrity: (operation, target) => `Object.${operation.level}(${target})`,
  length: (operation, target) => `${target}.length = ${operation.length}`,
  mapDelete: (operation, target) => `${target}.delete(${formatKeySpec(operation.key)})`,
  mapSet: (operation, target) =>
    `${target}.set(${formatKeySpec(operation.key)}, ${formatSpec(operation.value)})`,
  pop: (_operation, target) => `${target}.pop()`,
  prototype: (operation, target) => `Object.setPrototypeOf(${target}, ${operation.prototype})`,
  push: (operation, target) => `${target}.push(${formatSpec(operation.value)})`,
  resize: (operation, target) => `${target}.resize(${operation.length})`,
  reverse: (_operation, target) => `${target}.reverse()`,
  set: (operation, target) =>
    `${target}${formatKey(operation.key)} = ${formatSpec(operation.value)}`,
  setAdd: (operation, target) => `${target}.add(${formatSpec(operation.value)})`,
  setDelete: (operation, target) => `${target}.delete(${formatKeySpec(operation.key)})`,
  setTime: (operation, target) => `${target}.setTime(${operation.time})`,
  shift: (_operation, target) => `${target}.shift()`,
  splice: (operation, target) =>
    `${target}.splice(${[operation.start, operation.deleteCount, ...operation.values.map((value) => formatSpec(value))].join(', ')})`,
  unshift: (operation, target) => `${target}.unshift(${formatSpec(operation.value)})`,
}

const formatRecipe = (recipe: Recipe): string[] =>
  recipe.operations.map((operation, index) => {
    const format = FORMATTERS[operation.kind] as (operation: Operation, target: string) => string
    return `  ${format(operation, formatPath(operation.target))} -> ${recipe.outcomes[index]}`
  })

/* ----------------------------------------------------------------------------------- cases */

const PRODUCE_GRAPH: GraphOptions = {
  accessors: true,
  attributes: true,
  nodes: 8,
  plainRoot: false,
  rootKinds: CONTAINER_KINDS,
  throwingSetters: true,
}

const RECONCILE_GRAPH: GraphOptions = {
  ...PRODUCE_GRAPH,
  plainRoot: true,
  throwingSetters: false,
}

type Reconcile = (current: unknown, next: unknown) => unknown

type ReturnSpec = { kind: 'path'; path: Path } | { kind: 'root' } | { kind: 'wrap'; path: Path }

/** What the recipe returns: mostly the draft, sometimes a part of it, or a new object holding
 * the draft and a part of it. */
function planReturn(random: Random, root: unknown): ReturnSpec {
  const roll = random.next()
  if (roll < 0.8) return { kind: 'root' }
  const { path } = random.pick(survey(root).located)
  return { kind: roll < 0.9 ? 'path' : 'wrap', path }
}

function buildReturn(spec: ReturnSpec, root: unknown): unknown {
  if (spec.kind === 'root') return root
  const part = resolvePath(root, spec.path)
  return spec.kind === 'path' ? part : { part, root }
}

const sameOutcomes = (expected: Recipe, actual: Recipe): string | undefined => {
  const index = expected.outcomes.findIndex((outcome, at) => outcome !== actual.outcomes[at])
  if (index === -1) return undefined
  return `operation ${index} gave ${actual.outcomes[index]} on the draft and ${expected.outcomes[index]} natively`
}

/** Whether `value` still equals its copy `before` and holds the same objects. */
function unchangedFailure(
  before: unknown,
  value: unknown,
  copies: ReadonlyMap<object, object>,
  name: string,
): string | undefined {
  const { failure, images } = compareGraphs(before, value, exactPolicy)
  if (failure !== undefined) return `${name} changed: ${failure}`
  for (const [original, copy] of copies)
    if (images.get(copy) !== original) return `${name} holds a different object`
  return undefined
}

/** An object the recipe adds stays unchanged; the result holds it unless the recipe changed it
 * (README: Object identity, Objects the recipe adds). */
function addedFailure(native: Recipe, replayed: Recipe, tracker: Tracker): string | undefined {
  for (const [index, { copies, template }] of replayed.created.entries()) {
    const { failure } = compareGraphs(template, copies.get(template), exactPolicy)
    if (failure !== undefined) return `added value ${index} changed: ${failure}`
    for (const [node, copy] of native.created[index].copies) tracker.pair(copy, copies.get(node)!)
  }
  return undefined
}

/** The result matches the native one, with unchanged parts the original objects and changed
 * parts new (README: Object identity, Undone edits). */
function produceFailure(expected: unknown, result: unknown, tracker: Tracker): string | undefined {
  const changed = tracker.changed(expected)
  const { failure, images } = compareGraphs(expected, result, producePolicy(tracker.kept))
  if (failure !== undefined) return failure
  for (const [node, image] of images) {
    const source = tracker.identity.get(node)
    if (source === undefined) continue
    if (!changed.has(node) && image !== source)
      return `an unchanged ${kindOf(node)} is not the original object`
    if (changed.has(node) && tracker.kept.has(image))
      return `a changed ${kindOf(node)} reuses an original object`
  }
  return undefined
}

/**
 * One seeded `produce` case: the recipe runs natively on a plain copy of `current` and then on
 * the draft. The function under test is a parameter, so the fixture does not import the library.
 */
export function checkProduceCase(
  seed: number,
  produce: (current: unknown, recipe: (draft: unknown) => unknown) => unknown,
): string | undefined {
  const random = new Random(seed)
  const current = generateGraph(random, PRODUCE_GRAPH)
  const beforeCopies = new Map<object, object>()
  const before = deepCopy(current, beforeCopies)
  const nativeCopies = new Map<object, object>()
  const native = deepCopy(current, nativeCopies)
  const tracker = new Tracker()
  for (const [original, copy] of nativeCopies) tracker.record(copy, original)
  const recipe = planRecipe(random, native, 'produce', PRODUCE_GRAPH, ({ copies }) => {
    for (const copy of copies.values()) tracker.record(copy)
  })
  const returned = planReturn(random, native)
  const expected = buildReturn(returned, native)
  let replayed: Recipe | undefined
  const result = produce(current, (draft) => {
    replayed = replayRecipe(draft, recipe.operations)
    return buildReturn(returned, draft)
  })
  const failure =
    sameOutcomes(recipe, replayed!) ??
    unchangedFailure(before, current, beforeCopies, 'current') ??
    addedFailure(recipe, replayed!, tracker) ??
    produceFailure(expected, result, tracker)
  if (failure === undefined) return undefined
  const shown = returned.kind === 'root' ? 'root' : `${returned.kind} ${formatPath(returned.path)}`
  const recipeLines = formatRecipe(recipe)
  return [
    failure,
    'current:',
    describeGraph(before),
    'recipe:',
    ...recipeLines,
    `return: ${shown}`,
  ].join('\n')
}

/**
 * The positions where `reconcile` must leave an object of `current`, walking the pairs it matches
 * from the root (README: Update objects in place, Object identity):
 *
 * - matched: a current object and a next object that is not one of current's, of the same type,
 *   each held only at this position, the current one updatable in place;
 * - already in place: the same object in both at a property or index of a matched pair, held only
 *   there in each. The README exempts an object that reaches `current` or `next`, and one inside a
 *   `Map` or `Set` entry that is not itself in place; this leaves out every object reachable from
 *   an entry of `next`, since a moved object then falls under its rule for one object at two
 *   positions instead.
 */
function keptPositions(current: object, next: object): Located[] {
  const { inPlace, matched } = keepingRules(current, next)
  const positions: Located[] = [{ path: [], value: current }]
  // The flag marks pairs at or below a `Map` or `Set` entry, where nothing is already in place.
  const pending: Array<[object, object, Path, boolean]> = [[current, next, [], false]]
  for (const [left, right, path, inEntry] of pending)
    for (const [a, b, step] of matchedChildren(left, right)) {
      const at = [...path, step]
      const entry = inEntry || step.kind !== 'key'
      const kept = a === b ? !entry && inPlace(a) : matched(a, b)
      if (kept) positions.push({ path: at, value: a })
      if (kept && a !== b) pending.push([a, b, at, entry])
    }
  return positions
}

/** The two rules of `keptPositions`, for the pairs below a matched pair. */
function keepingRules(current: object, next: object) {
  const currentCounts = referenceCounts(current)
  const nextCounts = referenceCounts(next)
  const inEntries = new Set<object>()
  for (const node of reachable(next))
    if (node instanceof Map || node instanceof Set)
      facetOf(node).children(node, (child) => {
        for (const inner of reachable(child)) inEntries.add(inner)
      })
  const once = (node: object): boolean =>
    currentCounts.get(node) === 1 && nextCounts.get(node) === 1
  return {
    inPlace: (node: object): boolean =>
      once(node) &&
      !inEntries.has(node) &&
      !reachable(node).some((inner) => inner === current || inner === next),
    matched: (left: object, right: object): boolean =>
      currentCounts.get(left) === 1 &&
      !currentCounts.has(right) &&
      nextCounts.get(right) === 1 &&
      kindOf(left) === kindOf(right) &&
      isUpdatable(left),
  }
}

/** Counts the references to each node, the root's own reference included. */
function referenceCounts(root: unknown): Map<object, number> {
  const counts = new Map<object, number>()
  const count = (value: unknown): void => {
    if (isNode(value)) counts.set(value, (counts.get(value) ?? 0) + 1)
  }
  count(root)
  for (const node of reachable(root)) facetOf(node).children(node, count)
  return counts
}

/** Whether `reconcile` can update a node in place whatever `next` holds: a date, `Map` or `Set`,
 * whose contents freezing does not protect, or an extensible object or array whose properties
 * are all writable, enumerable and configurable data properties. */
function isUpdatable(node: object): boolean {
  if (node instanceof Date || node instanceof Map || node instanceof Set) return true
  if (!isContainer(node) || !Object.isExtensible(node)) return false
  return Reflect.ownKeys(node).every((key) =>
    Array.isArray(node) && key === 'length'
      ? descriptorOf(node, key).writable === true
      : sameAttributes({ ...PLAIN_DATA, value: 0 }, descriptorOf(node, key)),
  )
}

/** The node pairs at the positions `reconcile` matches by key, index or entry order. */
function matchedChildren(left: object, right: object): Array<[object, object, Step]> {
  const kind = kindOf(left)
  if (kind !== kindOf(right)) return []
  const pairs =
    kind === 'array' || kind === 'object'
      ? propertyPairs(left, right)
      : entryPairs(left, right, kind)
  return pairs.filter((pair): pair is [object, object, Step] => isNode(pair[0]) && isNode(pair[1]))
}

/** The values of the data properties that `right` has and `left` has too, by key. */
function propertyPairs(left: object, right: object): Array<[unknown, unknown, Step]> {
  const pairs: Array<[unknown, unknown, Step]> = []
  for (const key of Reflect.ownKeys(right)) {
    const a = Reflect.getOwnPropertyDescriptor(left, key)
    const b = descriptorOf(right, key)
    if (key !== 'length' && a !== undefined && 'value' in a && 'value' in b)
      pairs.push([a.value, b.value, keyStep(left, key)])
  }
  return pairs
}

const entryValues = (node: object): unknown[] =>
  node instanceof Map ? [...(node as Map<unknown, unknown>).values()] : membersOf(node)

/** The `Map` values or `Set` members of two collections, by entry order. */
function entryPairs(left: object, right: object, kind: Kind): Array<[unknown, unknown, Step]> {
  if (kind !== 'map' && kind !== 'set') return []
  const step = kind === 'map' ? 'mapValue' : 'setMember'
  const others = entryValues(right)
  return entryValues(left)
    .slice(0, others.length)
    .map((value, index) => [value, others[index], { index, kind: step }])
}

/** Whether `error` is the rejection of a call that would change `next`. */
const wouldChangeNext = (error: unknown): boolean =>
  (error as { cause?: { type?: unknown } } | undefined)?.cause?.type ===
  'PublicationWouldChangeNext'

/** Runs `reconcile` and compares the result with the copy `expected` of `next`; when `next` holds
 * objects of `current`, a rejection because the call would change `next` is no failure. */
function reconcileFailure(
  current: object,
  next: unknown,
  expected: unknown,
  reconcile: Reconcile,
  shared = false,
): string | undefined {
  const states = recordStates(current)
  const positions = keptPositions(current, next as object)
  let result: unknown
  try {
    result = reconcile(current, next)
  } catch (error) {
    return shared && wouldChangeNext(error) ? undefined : `reconcile threw ${String(error)}`
  }
  if (result !== current) return 'reconcile did not return current'
  const { failure } = compareGraphs(expected, result, reconcilePolicy(states))
  if (failure !== undefined) return failure
  const lost = positions.find(({ path, value }) => resolvePath(result, path) !== value)
  if (lost === undefined) return undefined
  return `${formatPath(lost.path)} is not the kept ${kindOf(lost.value)} of current`
}

/** One seeded `reconcile` case: `next` is a native edit of a plain copy of `current`. */
export function checkReconcileCase(
  seed: number,
  reconcile: (current: unknown, next: unknown) => unknown,
): string | undefined {
  const random = new Random(seed)
  const current = generateGraph(random, RECONCILE_GRAPH)
  const next = deepCopy(current)
  const recipe = planRecipe(random, next, 'next', RECONCILE_GRAPH)
  const before = deepCopy(current)
  const nextCopies = new Map<object, object>()
  const expected = deepCopy(next, nextCopies)
  // `reconcile` does not write to `next`, which shares no object with `current`.
  const failure =
    reconcileFailure(current, next, expected, reconcile) ??
    unchangedFailure(expected, next, nextCopies, 'next')
  if (failure === undefined) return undefined
  const sections = ['current:', describeGraph(before), 'next, from a copy of current:']
  return [failure, ...sections, ...formatRecipe(recipe), describeGraph(expected)].join('\n')
}

/**
 * One seeded case of README "Apply a recipe in place": `next` is `produce(current, recipe)`, which
 * holds the objects of `current` that the recipe left unchanged, at their positions or moved.
 * `reconcile` either reaches `next` or throws because it would change `next`; `next` stays as it
 * was in both cases.
 */
export function checkRecipeInPlaceCase(
  seed: number,
  produce: (current: unknown, recipe: (draft: unknown) => unknown) => unknown,
  reconcile: (current: unknown, next: unknown) => unknown,
): string | undefined {
  const random = new Random(seed)
  const current = generateGraph(random, RECONCILE_GRAPH)
  const recipe = planRecipe(random, deepCopy(current), 'produce', RECONCILE_GRAPH)
  const next = produce(current, (draft) => {
    replayRecipe(draft, recipe.operations)
    return draft
  })
  const before = deepCopy(current)
  const nextCopies = new Map<object, object>()
  const expected = deepCopy(next, nextCopies)
  const failure =
    reconcileFailure(current, next, expected, reconcile, true) ??
    unchangedFailure(expected, next, nextCopies, 'next')
  if (failure === undefined) return undefined
  const sections = ['current:', describeGraph(before), 'recipe:', ...formatRecipe(recipe)]
  return [failure, ...sections, 'next, the result of produce:', describeGraph(expected)].join('\n')
}
