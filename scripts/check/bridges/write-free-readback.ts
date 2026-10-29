import assert from 'node:assert/strict'
import { integerIn, jsonObject, oracleCorpus, type Oracle } from '../oracle'
import { matchesKind } from '../../../src/adapters/recognition'
import { atomValue, isNode } from '../../../src/graph/edge'
import { capture } from '../../../src/publication/capture'
import { reconcile } from '../../../src/reconcile'
import { publicationTypes } from '../../../src/types/builtins'

const NAMES = ['a', 'b', 'c']
const WANTED: ReadonlyArray<ReadonlyArray<number | undefined>> = [
  [1, 2],
  [1, undefined],
]

/** Traps a proxy saw, by name, and whether any wrote. */
interface Traps {
  counts: Map<string, number>
  wrote: boolean
}

const WRITES = new Set(['defineProperty', 'deleteProperty', 'set'])

/** A proxy over `target` that counts its traps; `get` and `has` are counted per key. */
function observed(target: object, traps: Traps): object {
  const count = (name: string): void => {
    traps.counts.set(name, (traps.counts.get(name) ?? 0) + 1)
    if (WRITES.has(name.split(':')[0])) traps.wrote = true
  }
  return new Proxy(target, {
    defineProperty(object, key, descriptor) {
      count('defineProperty')
      return Reflect.defineProperty(object, key, descriptor)
    },
    deleteProperty(object, key) {
      count('deleteProperty')
      return Reflect.deleteProperty(object, key)
    },
    get(object, key, receiver) {
      count(`get:${String(key)}`)
      return Reflect.get(object, key, receiver) as unknown
    },
    ownKeys(object) {
      count('ownKeys')
      return Reflect.ownKeys(object)
    },
    set(object, key, value, receiver) {
      count('set')
      return Reflect.set(object, key, value, receiver)
    },
  })
}

/** The runtime's readback of `current` against `next` before any write: the kind check and
 * `matches` that `publishGraph`'s readback asks of the root, whose edges here are primitives. */
function readbackAccepts(current: object, next: object): boolean {
  const graph = capture(publicationTypes, next)
  assert.ok(isNode(graph.root))
  const node = graph.nodes[graph.root.node]
  return (
    matchesKind(publicationTypes, current, node.layout.kind) &&
    publicationTypes.policies[node.layout.kind].matches(
      node,
      current,
      (actual, wanted) => !isNode(wanted) && Object.is(actual, atomValue(wanted)),
    )
  )
}

/** Reconciles a counted `current` onto `next`, then checks the raw `current` equals `next`. */
function run(current: object, next: object): Traps {
  const traps: Traps = { counts: new Map(), wrote: false }
  reconcile(observed(current, traps), next)
  assert.deepEqual(current, next, 'reconcile reaches next')
  return traps
}

/** The object a row describes: each listed key holding its value, mapped by `valueOf`. */
function objectRow<T>(row: Record<string, unknown>, valueOf: (value: number) => T): object {
  assert.ok(Array.isArray(row.keys) && Array.isArray(row.values))
  const current: Record<string, unknown> = {}
  for (const [index, key] of row.keys.entries())
    current[NAMES[integerIn(key, 0, 2)]] = valueOf(integerIn(row.values[index], 0, 9))
  return current
}

function checkObject(row: Record<string, unknown>): boolean {
  const current = objectRow(row, (value) => value)
  const next = { a: 1, b: 2 }
  assert.equal(
    readbackAccepts(current, next),
    row.accepts,
    `object ${JSON.stringify(current)} readback`,
  )
  const traps = run(current, next)
  // The preflight lists the keys once (names and symbols); a readback lists them again.
  const elided = traps.counts.get('ownKeys') === 2
  assert.equal(elided, row.writeFree, `object ${JSON.stringify(current)} readback elided`)
  assert.equal(!traps.wrote, row.writeFree, `object ${JSON.stringify(current)} wrote nothing`)
  assert.equal(row.accepts, row.writeFree, 'write-free exactly when readback accepts')
  return elided
}

/** An array holding each defined value at its index and a hole for each undefined. */
function sparse(elements: readonly unknown[]): unknown[] {
  const array: unknown[] = []
  array.length = elements.length
  for (const [index, element] of elements.entries())
    if (element !== undefined) array[index] = element
  return array
}

/** The array a row describes, each element mapped by `valueOf`. */
function arrayRow(row: Record<string, unknown>, valueOf: (value: number) => unknown): unknown[] {
  assert.ok(Array.isArray(row.elements))
  return row.elements.map((element) =>
    element === null ? undefined : valueOf(integerIn(element, 0, 9)),
  )
}

const wantedOf = (row: Record<string, unknown>): ReadonlyArray<number | undefined> =>
  WANTED[integerIn(row.wanted, 0, WANTED.length - 1)]

function checkArray(row: Record<string, unknown>): boolean {
  const current = sparse(arrayRow(row, (value) => value))
  const next = sparse(wantedOf(row))
  assert.equal(
    readbackAccepts(current, next),
    row.accepts,
    `array ${JSON.stringify(row.elements)} readback`,
  )
  const traps = run(current, next)
  // Publication reads the length once; a readback reads it again.
  const elided = traps.counts.get('get:length') === 1
  assert.equal(elided, row.writeFree, `array ${JSON.stringify(row.elements)} readback elided`)
  assert.equal(!traps.wrote, row.writeFree, `array ${JSON.stringify(row.elements)} wrote nothing`)
  assert.equal(row.accepts, row.writeFree, 'write-free exactly when readback accepts')
  return elided
}

/** One frozen object per value. An object at its own position is kept, and one holding another
 * value cannot take that value, so a key needs a write exactly when its object differs, as Lean
 * compares values. */
const pool = new Map<number, object>()
const objectOf = (value: number): object => {
  let object = pool.get(value)
  if (object === undefined) pool.set(value, (object = Object.freeze({ value })))
  return object
}

/** Reads of a requested key: capture's, which publication decides from, and readback's after any
 * write; a requested key that `current` lacks is read by readback alone, an unrequested one never. */
const expectedReads = (requested: boolean, held: boolean, writeFree: unknown): number =>
  !requested ? 0 : !held || writeFree === true ? 1 : 2

function assertReads(traps: Traps, key: PropertyKey, expected: number, row: unknown): void {
  assert.equal(
    traps.counts.get(`get:${String(key)}`) ?? 0,
    expected,
    `${JSON.stringify(row)} reads ${String(key)}`,
  )
}

/**
 * The same object row with object values: capture reads each requested key the current object
 * holds, publication decides from that read (`WriteFreeReadback.publishPre`), and only readback,
 * which follows any write, reads again.
 */
function checkObjectReads(row: Record<string, unknown>): void {
  const current = objectRow(row, objectOf)
  const held = new Set(Object.keys(current))
  const traps = run(current, { a: objectOf(1), b: objectOf(2) })
  for (const name of NAMES)
    assertReads(traps, name, expectedReads(name !== 'c', held.has(name), row.writeFree), row)
}

/** The same array row with object elements, read as `checkObjectReads` reads keys; publication
 * decides each from capture's read (`WriteFreeReadback.publishSeen`). */
function checkArrayReads(row: Record<string, unknown>): void {
  const wanted = wantedOf(row)
  const elements = arrayRow(row, objectOf)
  const traps = run(
    sparse(elements),
    sparse(wanted.map((element) => (element === undefined ? undefined : objectOf(element)))),
  )
  for (let index = 0; index < wanted.length; index += 1) {
    const requested = wanted[index] !== undefined
    assertReads(
      traps,
      index,
      expectedReads(requested, elements[index] !== undefined, row.writeFree),
      row,
    )
  }
}

/** Checks one row's readback before any write, elision and reads; whether its readback was
 * elided. */
function checkRow(row: Record<string, unknown>): boolean {
  const object = 'keys' in row
  const elided = object ? checkObject(row) : checkArray(row)
  if (object) checkObjectReads(row)
  else checkArrayReads(row)
  return elided
}

/** Compares the readback, its elision and the reads of `current` with Lean's
 * `Property.WriteFreeReadback`. */
export async function checkWriteFreeReadbackRuntime(oracle: Oracle): Promise<void> {
  // 46 ordered key subsets with their values and 53 arrays of length up to three.
  const rows = await oracleCorpus(oracle, 'WriteFreeReadback', 99, 64 * 1024)
  let elided = 0
  for (const line of rows) if (checkRow(jsonObject(JSON.parse(line)))) elided += 1
  console.log(
    `WriteFreeReadback Lean/native bridge: ${rows.length} publications whose readback before ` +
      `any write answers as Lean's matches, ${elided} write-free with the readback elided, every ` +
      'other one read back; each requested object value of `current` read once without a write ' +
      'and twice with one',
  )
}
