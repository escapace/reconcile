import assert from 'node:assert/strict'
import { deserialize } from '../../../src/deserialize'
import { serialize } from '../../../src/serialize'
import { requiredMaxBytes } from '../../../src/required-max-bytes'
import { isReconcileError } from '../../../src/error'
import type { Oracle } from '../oracle'
// Documents travel as JSON text, as they do between applications.
const decodeText = (text: string): unknown => deserialize(JSON.parse(text), { maxBytes: Infinity })
interface Model {
  root: Token
  rows: Row[]
}
interface Response {
  expanded: Model
  ok: boolean
  reemitted: unknown
  words: number
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
// Canonical bigint text, computed from the value rather than read from the wire.
const hexText = (value: bigint): string =>
  value < 0n ? `-0x${(-value).toString(16)}` : `0x${value.toString(16)}`
function atom(value: unknown): Token {
  if (typeof value === 'bigint') return [0, JSON.stringify({ bigint: hexText(value) })]
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
  // Keys and strings measured in UTF-16 code units; keys in the order Lean's object model keeps.
  // Lean strings cannot hold a lone surrogate, so none appears here.
  '""',
  '"\\ud83d\\ude00abcd"',
  '{"":"","a":["😀",{"b":[]}],"😀😀😀":"x"}',
  '[[],{},[[""]],"abcde"]',
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
// Size.lean accounting, executed by the oracle: the runtime accepts the document at exactly
// eight bytes per word and rejects it one byte below, and requiredMaxBytes measures that limit
// (accepts_iff_bytes) without modifying the document. Decoding takes ownership, so each call
// gets its own copy.
function checkWords(document: unknown, words: number, label: string): void {
  assert(Number.isSafeInteger(words) && words > 0, label)
  const measured = structuredClone(document)
  assert.equal(requiredMaxBytes(measured, { maxBytes: Infinity }), 8 * words, label)
  assert.deepStrictEqual(measured, document, label)
  deserialize(structuredClone(document), { maxBytes: 8 * words })
  assert.throws(
    () => deserialize(structuredClone(document), { maxBytes: 8 * words - 1 }),
    (error) => isReconcileError(error) && error.cause.type === 'DeserializeLimitExceeded',
    label,
  )
}
// A root without nodes is a single literal: any JSON value, as JSON.parse produced it.
function checkLiteralRoot(document: string, result: Response): void {
  if (!result.ok) {
    assert.throws(() => decodeText(document))
    return
  }
  checkWords(JSON.parse(document), result.words, document)
  assert.deepEqual(normalizeModel(result.expanded), sourceModel(decodeText(document)))
  assert.deepEqual(result.reemitted, JSON.parse(document))
}
/** Lean's response to each wire, in order. */
async function ask(run: Oracle, wires: readonly unknown[]): Promise<Response[]> {
  const input = JSON.stringify(wires.map((wire) => ({ wire })))
  const responses = JSON.parse(await run('Serialization', { input })) as Response[]
  assert.equal(responses.length, wires.length)
  return responses
}

async function checkLiteralRoots(run: Oracle): Promise<void> {
  const documents = literalDocuments()
  const results = await ask(
    run,
    documents.map((document) => JSON.parse(document) as unknown),
  )
  for (let index = 0; index < results.length; index++)
    checkLiteralRoot(documents[index], results[index])
}
// Lean's JSON numbers have no -0 and no overflow to infinity, so those roots are checked against
// JSON.parse at runtime only; every other literal root is compared with the Lean expansion.
function literalDocuments(): string[] {
  const documents = scalarTexts.map((text) => `[${text}]`)
  for (const document of documents) {
    const value = (JSON.parse(document) as unknown[])[0]
    if (unsupportedRawNumber(value)) assert(Object.is(decodeText(document), value), document)
  }
  return documents.filter(
    (document) => !unsupportedRawNumber((JSON.parse(document) as unknown[])[0]),
  )
}

// Positional.lean encodeControl: layout ids, the shape count, framed shapes, framed layouts.
function wire([shapes, layouts, ids, payloads]: unknown[][]): unknown[] {
  const control: unknown[] = [...ids, shapes.length]
  for (const entry of [...shapes, ...layouts] as unknown[][]) control.push(entry.length, ...entry)
  return [control, payloads]
}

export async function checkSerializationRuntime(run: Oracle): Promise<void> {
  const wires = good.map((x) => serialize(x.input))
  const responses = await ask(run, wires)
  for (let index = 0; index < good.length; index++) {
    const expected = sourceModel(good[index].input)
    const r = responses[index]
    assert.equal(r.ok, true, JSON.stringify({ name: good[index].name, r }))
    assert.deepEqual(normalizeModel(r.expanded), expected, good[index].name)
    // The proved encoder re-emits exactly the runtime document: it is canonical.
    assert.deepEqual(r.reemitted, wires[index], good[index].name)
    checkWords(wires[index], r.words, good[index].name)
  }
  // Documents in table notation [shapes, layouts, layout ids, payloads], framed by `wire`.
  const invalid = [
    [[], [], [], []],
    [[], [[2, 0]], [0], [[1]]],
    [[], [[2, 0]], [0], [[0.5]]],
    [[], [[2, 1]], [0], [[1]]],
    [[], [[2, 1, 0]], [0], [[1, 0, 1]]],
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
    [[['x']], [[0, 1]], [0], [[1]]],
    [[], [[2], [2]], [0, 1], [[], []]],
    [[], [[2], [13]], [1, 0], [[], []]],
    [[], [[3]], [0], [[2, [2], [1, 2]]]],
    [[], [[3]], [0], [[2, [], [1, 2]]]],
    [[], [[3]], [0], [[2, [0, 3], []]]],
    [[], [[3]], [0], [[3, [1, 0, 1], [1, 2]]]],
    [[], [[3]], [0], [[3, [1], [1, 2]]]],
    [[], [[18]], [0], [['-0x0']]],
    [[], [[18]], [0], [['0x01']]],
    [[], [[18]], [0], [['0xFF']]],
    [[], [[18]], [0], [['ff']]],
    [[], [[18]], [0], [['1']]],
    [[], [[18]], [0], [[' 0x1']]],
    [[], [[18]], [0], [['0x']]],
    [[], [[18]], [0], [['-0x']]],
    [[], [[18]], [0], [['0X1']]],
    [[], [[18]], [0], [['0xg']]],
    [[], [[13, 0]], [0], [[]]],
    [[], [[2, 0], [2]], [0, 1, 1], [[2, 1], [], []]],
    [[], [[2, 0], [2]], [0, 1], [[0], []]],
    [[], [[2, 0], [2]], [0, 1, 1], [[1], [], []]],
  ].map(wire)
  invalid.push([-6, [], [[0, 0]]], [[0], [[1]]])
  const rejected = await ask(run, invalid)
  for (let index = 0; index < invalid.length; index++) {
    assert.equal(rejected[index].ok, false, JSON.stringify(invalid[index]))
    assert.throws(() => decodeText(JSON.stringify(invalid[index])), JSON.stringify(invalid[index]))
  }
  // Tables are used as given: repeated, reordered or unused entries and a repeated key keep one
  // meaning, which Lean and the runtime must agree on.
  const accepted = [
    [[['x']], [[2]], [0], [[]]],
    [[['x', 'x']], [[0, 0]], [0], [[1, 2]]],
    [[], [[2], [13]], [0], [[]]],
    [[], [[2, 0], [13]], [0, 1, 1], [[1, 2], [], []]],
    [[], [[2, 0], [18]], [0, 1, 1], [[1, 2], ['0x5'], ['0x5']]],
    [[], [[2, 0], [2], [2]], [0, 1, 2], [[1, 2], [], []]],
    // A literal is any JSON value: objects and arrays decode to fresh, unshared values.
    [[], [[2]], [0], [[[1]]]],
    [[], [[2]], [0], [[{}, [], [{ a: [1, { b: null }] }]]]],
    [[['x', 'x']], [[0, 0]], [0], [[[1], 2]]],
    [[], [[3]], [0], [[3, [1, 1], [[1], { a: 'b' }]]]],
    [
      [['b'], ['a']],
      [
        [0, 1],
        [0, 0, 0],
      ],
      [1, 0],
      [[1], [5]],
    ],
  ].map(wire)
  const agreed = await ask(run, accepted)
  for (let index = 0; index < accepted.length; index++) {
    const text = JSON.stringify(accepted[index])
    assert.equal(agreed[index].ok, true, text)
    assert.deepEqual(normalizeModel(agreed[index].expanded), sourceModel(decodeText(text)), text)
    checkWords(accepted[index], agreed[index].words, text)
  }
  await checkLiteralRoots(run)
  console.log(
    `Serialization Lean bridge: ${good.length} graphs re-emitted exactly, ${invalid.length} malformed and ${accepted.length} non-canonical documents; every accepted document's size limit agrees and is measured`,
  )
}
