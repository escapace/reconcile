import assert from 'node:assert/strict'
import { integerIn, jsonObject, oracleCorpus, type Oracle } from './lean-oracle'
import { reconcile } from '../src/reconcile'

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

/** Reconciles a counted `current` onto `next`, then checks the raw `current` equals `next`. */
function run(current: object, next: object): Traps {
  const traps: Traps = { counts: new Map(), wrote: false }
  reconcile(observed(current, traps), next)
  assert.deepEqual(current, next, 'reconcile reaches next')
  return traps
}

function checkObject(row: Record<string, unknown>): boolean {
  assert.ok(Array.isArray(row.keys) && Array.isArray(row.values))
  const current: Record<string, unknown> = {}
  for (const [index, key] of row.keys.entries())
    current[NAMES[integerIn(key, 0, 2)]] = integerIn(row.values[index], 0, 9)
  const traps = run(current, { a: 1, b: 2 })
  // The preflight lists the keys once (names and symbols); a readback lists them again.
  const elided = traps.counts.get('ownKeys') === 2
  assert.equal(elided, row.writeFree, `object ${JSON.stringify(current)} readback elided`)
  assert.equal(!traps.wrote, row.writeFree, `object ${JSON.stringify(current)} wrote nothing`)
  assert.equal(row.accepts, row.writeFree, 'write-free exactly when readback accepts')
  return elided
}

/** An array holding each defined value at its index and a hole for each undefined. */
function sparse(elements: ReadonlyArray<number | undefined>): unknown[] {
  const array: unknown[] = []
  array.length = elements.length
  for (const [index, element] of elements.entries())
    if (element !== undefined) array[index] = element
  return array
}

function checkArray(row: Record<string, unknown>): boolean {
  const wanted = WANTED[integerIn(row.wanted, 0, WANTED.length - 1)]
  assert.ok(Array.isArray(row.elements))
  const current = sparse(
    row.elements.map((element) => (element === null ? undefined : integerIn(element, 0, 9))),
  )
  const next = sparse(wanted)
  const traps = run(current, next)
  // Publication reads the length once; a readback reads it again.
  const elided = traps.counts.get('get:length') === 1
  assert.equal(elided, row.writeFree, `array ${JSON.stringify(row.elements)} readback elided`)
  assert.equal(!traps.wrote, row.writeFree, `array ${JSON.stringify(row.elements)} wrote nothing`)
  assert.equal(row.accepts, row.writeFree, 'write-free exactly when readback accepts')
  return elided
}

/** Compares readback elision with Lean's `Property.WriteFreeReadback`. */
export async function checkWriteFreeReadbackRuntime(oracle: Oracle): Promise<void> {
  // 46 ordered key subsets with their values and 53 arrays of length up to three.
  const rows = await oracleCorpus(oracle, 'WriteFreeReadback', 99, 64 * 1024)
  let elided = 0
  for (const line of rows) {
    const row = jsonObject(JSON.parse(line))
    if ('keys' in row ? checkObject(row) : checkArray(row)) elided += 1
  }
  console.log(
    `WriteFreeReadback Lean/native bridge: ${rows.length} publications, ${elided} write-free ` +
      'with the readback elided, every other one read back',
  )
}
