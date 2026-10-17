import assert from 'node:assert/strict'
import { parse } from '../src/parse'
import { stringify } from '../src/stringify'
import type { Oracle } from './lean-oracle'
interface Model {
  root: Token
  rows: Row[]
}
interface Response {
  expanded: Model
  ok: boolean
  reemitted: unknown
}
interface Row {
  edges: Array<[string, Token]>
  kind: string
  payload: string[]
}
type Token = [0, string] | [1, number]
const nullRecord = (): Record<string, unknown> => Object.create(null) as Record<string, unknown>
// Atoms name values independently of the wire: JSON scalars by their JSON text, shared scalar
// nodes by an object a literal can never be.
const scalarNames: Array<[unknown, string]> = [
  [undefined, 'undefined'],
  [NaN, 'NaN'],
  [Infinity, 'Infinity'],
  [-Infinity, '-Infinity'],
  [-0, '-0'],
]
function atom(value: unknown): Token {
  if (typeof value === 'bigint') return [0, JSON.stringify({ bigint: String(value) })]
  const name = scalarNames.find(([scalar]) => Object.is(scalar, value))?.[1]
  return [0, JSON.stringify(name === undefined ? value : { scalar: name })]
}
function sourceRow(value: object, token: (value: unknown) => Token): Row {
  const keys = Object.keys(value)
  const prototype: unknown = Object.getPrototypeOf(value)
  const edges: Array<[string, Token]> = keys.map((key) => [
    key,
    token((value as Record<string, unknown>)[key]),
  ])
  if (Array.isArray(value)) {
    assert.equal(prototype, Array.prototype)
    assert(keys.every((key) => /^(?:0|[1-9]\d*)$/.test(key) && Number(key) < value.length))
    return { edges, kind: 'array', payload: [String(value.length)] }
  }
  assert(prototype === Object.prototype || prototype === null, 'bridge domain')
  return { edges, kind: prototype === null ? 'nullObject' : 'object', payload: [] }
}
// Independent source extraction does not inspect codec tables or shape dictionaries.
function sourceModel(input: unknown): Model {
  const seen = new Map<object, number>()
  const queue: object[] = []
  const rows: Row[] = []
  function token(value: unknown): Token {
    if (value === null || typeof value !== 'object') return atom(value)
    if (!seen.has(value)) {
      seen.set(value, queue.length)
      queue.push(value)
    }
    return [1, seen.get(value)!]
  }
  const root = token(input)
  for (let index = 0; index < queue.length; index++) rows.push(sourceRow(queue[index], token))
  return { root, rows }
}
// Canonical root-reachable BFS numbering compares graphs independently of discovery order.
function normalizeModel(model: Model) {
  const ids = new Map<number, number>()
  const queue: number[] = []
  const rows: Row[] = []
  function token(t: Token): Token {
    if (t[0] !== 1) return normToken(t)
    if (!ids.has(t[1])) {
      ids.set(t[1], queue.length)
      queue.push(t[1])
    }
    return [1, ids.get(t[1])!]
  }
  const root = token(model.root)
  for (let index = 0; index < queue.length; index++) {
    const r = model.rows[queue[index]]
    rows.push({
      edges: r.edges.map(([k, t]) => [k, token(t)]),
      kind: r.kind,
      payload: r.payload,
    })
  }
  assert.equal(queue.length, model.rows.length, 'all bridge rows reachable')
  return { root, rows }
}
const normToken = (t: Token): Token => (t[0] === 0 ? [0, JSON.stringify(JSON.parse(t[1]))] : t)
const own = (o: object, k: string, v: unknown) =>
  Object.defineProperty(o, k, { configurable: true, enumerable: true, value: v, writable: true })
const good: Array<{ input: unknown; name: string }> = []
const add = (name: string, make: () => unknown) => good.push({ input: make(), name })
for (const [name, value] of [
  ['null', null],
  ['undefined', undefined],
  ['minuszero', -0],
  ['nan', NaN],
  ['infinity', Infinity],
  ['negativeinfinity', -Infinity],
  ['bigint', 123_456_789_012_345_678_901_234_567_890n],
  ['string', 'é\n"\\\u0000\u2028😀'],
  ['safeinteger', Number.MAX_SAFE_INTEGER],
] as Array<[string, unknown]>)
  add('root-' + name, () => value)
add('empty-record', () => ({}))
add('empty-array', () => [])
add('empty-null-record', () => nullRecord())
add('record-self-alias', () => {
  const a: Record<string, unknown> = {}
  a.self = a
  a.again = a
  return a
})
add('distinct-equal-nodes', () => {
  const a = { x: 1 }
  const b = { x: 1 }
  return { a, again: a, b }
})
add('dense-array-self', () => {
  const a: unknown[] = [1, null]
  a.push(a)
  return a
})
add('sparse-holes-vs-undefined', () => {
  const a = new Array<unknown>(9)
  a[2] = undefined
  a[5] = a
  return a
})
add('key-order-and-dangerous-keys', () => {
  const x = nullRecord()
  for (const k of [
    'b',
    'a',
    '10',
    '2',
    '__proto__',
    'constructor',
    'prototype',
    '',
    'a/b',
    'a.b',
    'é\u0000',
  ])
    own(x, k, k === '__proto__' ? x : k)
  return { plain: Object.assign({}, { a: 2, b: 1 }), x }
})
add('shared-shapes-different-prototypes', () => {
  const a = { x: 1, y: 2 }
  const b = Object.assign(nullRecord(), { x: 1, y: 2 })
  const reversed = {}
  own(reversed, 'y', 2)
  own(reversed, 'x', 1)
  return [a, b, a, b, reversed]
})
let state = 0x5a_17_c0_de
const random = () => {
  state ^= state << 13
  state ^= state >>> 17
  state ^= state << 5
  return (state >>> 0) / 4_294_967_296
}
const atoms = [
  null,
  true,
  false,
  0,
  1,
  -1,
  100,
  undefined,
  -0,
  NaN,
  Infinity,
  -Infinity,
  77n,
  '',
  'quote"',
  'line\n',
  'é😀',
]
function populate(value: Record<string, unknown> | unknown[], choose: () => unknown): void {
  if (Array.isArray(value)) populateArray(value, choose)
  else populateRecord(value, choose)
}
function populateArray(value: unknown[], choose: () => unknown): void {
  for (let index = 0; index < value.length; index++) if (random() < 0.65) value[index] = choose()
}
function populateRecord(value: Record<string, unknown>, choose: () => unknown): void {
  for (let index = 0; index < Math.floor(random() * 6); index++)
    own(value, ['k0', '__proto__', 'k2', 'constructor', '4'][index], choose())
}
function randomGraph(): unknown {
  const length = 2 + Math.floor(random() * 15)
  const pool = Array.from({ length }, randomNode)
  const choose = (): unknown =>
    random() < 0.6
      ? pool[Math.floor(random() * length)]
      : atoms[Math.floor(random() * atoms.length)]
  for (const value of pool) populate(value, choose)
  return { again: pool[0], all: pool }
}
function randomNode(): Record<string, unknown> | unknown[] {
  const kind = Math.floor(random() * 3)
  if (kind === 0) return {}
  if (kind === 1) return nullRecord()
  return new Array<unknown>(Math.floor(random() * 7))
}
for (let fixture = 0; fixture < 80; fixture++) add('seeded-' + fixture, randomGraph)
add('negative-data-and-extrema', () => [
  -1,
  -0.5,
  -Number.MIN_VALUE,
  -Number.MAX_VALUE,
  Number.MIN_SAFE_INTEGER - 2,
  Number.MAX_VALUE,
  Number.MIN_VALUE,
])

function unsupportedRawNumber(value: unknown): boolean {
  return typeof value === 'number' && (!Number.isFinite(value) || Object.is(value, -0))
}
const scalarTexts = [
  '-1',
  '-2',
  '-6',
  '-7',
  '-0.5',
  '-1.50',
  '-0.50000000000000001',
  '-1.00000000000000001',
  '-1.25',
  '[-1]',
  '[-7,-0.5]',
  '[-6,"123"]',
  '{}',
  '-0',
  '-1e-400',
  '-1e400',
  '1e400',
  '"-1"',
  '0',
  '1',
  '1e21',
  'true',
  'null',
]
// A root without nodes is a single literal; composites and non-JSON numbers are not literals.
// Signed zero and nonfinite raw numbers are outside the finite JSON number model.
function checkLiteralRoot(document: string, result: Response): void {
  if (!result.ok) {
    assert.throws(() => parse(document))
    return
  }
  assert.deepEqual(normalizeModel(result.expanded), sourceModel(parse(document)))
  assert.deepEqual(result.reemitted, JSON.parse(document))
}
async function checkLiteralRoots(run: Oracle): Promise<void> {
  const documents = literalDocuments()
  const requests = documents.map((document) => ({ wire: JSON.parse(document) as unknown }))
  const results = JSON.parse(
    await run('Serialization', [], { input: JSON.stringify(requests) }),
  ) as Response[]
  assert.equal(results.length, documents.length)
  for (let index = 0; index < results.length; index++)
    checkLiteralRoot(documents[index], results[index])
}
function literalDocuments(): string[] {
  const documents = scalarTexts.map((text) => `[${text}]`)
  for (const document of documents)
    if (unsupportedRawNumber((JSON.parse(document) as unknown[])[0]))
      assert.throws(() => parse(document))
  return documents.filter(
    (document) => !unsupportedRawNumber((JSON.parse(document) as unknown[])[0]),
  )
}

export async function checkSerializationRuntime(run: Oracle): Promise<void> {
  const wires = good.map((x) => JSON.parse(stringify(x.input)) as unknown)
  const responses = JSON.parse(
    await run('Serialization', [], { input: JSON.stringify(wires.map((wire) => ({ wire }))) }),
  ) as Response[]
  assert.equal(responses.length, good.length)
  for (let index = 0; index < good.length; index++) {
    const expected = sourceModel(good[index].input)
    const r = responses[index]
    assert.equal(r.ok, true, JSON.stringify({ name: good[index].name, r }))
    assert.deepEqual(normalizeModel(r.expanded), expected, good[index].name)
    // The proved encoder re-emits exactly the runtime document: it is canonical.
    assert.deepEqual(r.reemitted, wires[index], good[index].name)
  }
  const invalid = [
    [-6, [], [[0, 0]]],
    [[], [], [], []],
    [[], [[2, 0]], [0], [[1]]],
    [[], [[2, 0]], [0], [[0.5]]],
    [[], [[2, 1]], [0], [[1]]],
    [[], [[2, 1, 0]], [0], [[1, 0, 1]]],
    [[['x']], [[2]], [0], [[]]],
    [[['x', 'x']], [[0, 0]], [0], [[1, 2]]],
    [
      [['x'], ['x']],
      [
        [0, 0],
        [0, 1],
      ],
      [0, 1],
      [[1], [2]],
    ],
    [[['x']], [[0, 0]], [0], [[1, 2]]],
    [[], [[2], [2]], [0, 1], [[], []]],
    [[], [[2], [13]], [1, 0], [[], []]],
    [[], [[2], [13]], [0], [[]]],
    [[], [[3]], [0], [[2, [2], [1, 2]]]],
    [[], [[3]], [0], [[2, [], [1, 2]]]],
    [[], [[3]], [0], [[2, [0, 3], []]]],
    [[], [[3]], [0], [[3, [1, 0, 1], [1, 2]]]],
    [[], [[3]], [0], [[3, [1], [1, 2]]]],
    [[], [[2, 0], [13]], [0, 1, 1], [[1, 2], [], []]],
    [[], [[2, 0], [18]], [0, 1, 1], [[1, 2], ['5'], ['5']]],
    [[], [[18]], [0], [['-0']]],
    [[], [[18]], [0], [['01']]],
    [[], [[13, 0]], [0], [[]]],
    [[], [[2]], [0], [[[1]]]],
    [[], [[2]], [0], [[{}]]],
    [[[1]]],
    [[], [[2, 0], [2]], [0, 1, 1], [[2, 1], [], []]],
    [[], [[2, 0], [2]], [0, 1], [[0], []]],
    [[], [[2, 0], [2]], [0, 1, 1], [[1], [], []]],
  ]
  const rejected = JSON.parse(
    await run('Serialization', [], { input: JSON.stringify(invalid.map((wire) => ({ wire }))) }),
  ) as Response[]
  for (let index = 0; index < invalid.length; index++) {
    assert.equal(rejected[index].ok, false, JSON.stringify(invalid[index]))
    assert.throws(() => parse(JSON.stringify(invalid[index])), JSON.stringify(invalid[index]))
  }
  await checkLiteralRoots(run)
  console.log(
    `Serialization Lean bridge: ${good.length} graphs re-emitted exactly, ${invalid.length} malformed documents`,
  )
}
