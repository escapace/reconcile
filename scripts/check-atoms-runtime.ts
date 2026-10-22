import assert from 'node:assert/strict'
import { integerIn, jsonObject, oracleCorpus, type Oracle } from './lean-oracle'
import { isReconcileError } from '../src/error'
import { isAtomObject } from '../src/object-property'
import { produce } from '../src/produce'
import { reconcile } from '../src/reconcile'
import { serialize } from '../src/serialize'
import { snapshot } from '../src/snapshot'

/** The real chains of `AtomsOracle.tails`, from the first prototype to `null`, in its order. */
const tails: ReadonlyArray<readonly object[]> = [
  [],
  [Object.prototype],
  [Array.prototype, Object.prototype],
  ...[
    RegExp,
    Error,
    WeakMap,
    WeakSet,
    WeakRef,
    FinalizationRegistry,
    Promise,
    Number,
    String,
    Boolean,
    BigInt,
    Symbol,
    Blob,
  ].map((constructor) => [constructor.prototype as object, Object.prototype]),
  [TypeError.prototype, Error.prototype, Object.prototype],
  [File.prototype, Blob.prototype, Object.prototype],
  ...[Map, Set, Date, URL].map((constructor) => [
    constructor.prototype as object,
    Object.prototype,
  ]),
  [Uint8Array.prototype, Object.getPrototypeOf(Uint8Array.prototype) as object, Object.prototype],
]

/** Checks that each tail is the real chain of its first prototype. */
export function checkRealChains(tails: ReadonlyArray<readonly object[]>): void {
  for (const tail of tails) {
    const chain: object[] = []
    let prototype: object | null = tail[0] ?? null
    while (prototype !== null) {
      chain.push(prototype)
      prototype = Object.getPrototypeOf(prototype) as object | null
    }
    assert.deepEqual(chain, tail, 'real prototype chain')
  }
}

/** An object behind `depth` custom prototypes; the object and each custom level count their
 * `[[GetPrototypeOf]]` calls. */
function build(depth: number, tail: readonly object[], reads: { count: number }): object {
  let prototype: object | null = tail[0] ?? null
  for (let level = 0; level <= depth; level++) {
    const target = Object.create(prototype) as object
    prototype = new Proxy(target, {
      getPrototypeOf(object) {
        reads.count += 1
        return Reflect.getPrototypeOf(object)
      },
    })
  }
  return prototype
}

/** Every function keeps an atom by reference; `serialize` rejects it. */
function checkAtom(value: object): void {
  assert.equal((snapshot({ value }) as { value: unknown }).value, value, 'snapshot')
  const current: Record<string, unknown> = { value: 0 }
  reconcile(current, { value })
  assert.equal(current.value, value, 'reconcile')
  let read: unknown
  const result = produce({ other: 0, value }, (draft) => {
    read = draft.value
    draft.other = 1
    return draft
  })
  assert.equal(read, value, 'produce does not draft an atom')
  assert.equal(result.value, value, 'produce keeps an atom')
  assert.throws(
    () => serialize({ value }),
    (error) => isReconcileError(error) && error.cause.type === 'SerializeValueUnsupported',
  )
}

/** Compares one Lean classification with the runtime walk and, for atoms, every function. */
function checkRow(row: Record<string, unknown>): boolean {
  const depth = integerIn(row.depth, 0, 3)
  const tail = tails[integerIn(row.tail, 0, tails.length - 1)]
  const reads = { count: 0 }
  const value = build(depth, tail, reads)
  const atomic = isAtomObject(value)
  assert.equal(atomic, row.atomic, 'classification')
  // The proxies see the value's read and one per custom level the walk passes.
  assert.equal(reads.count, Math.min(integerIn(row.reads, 1, 32), depth + 1), 'prototype reads')
  if (atomic) checkAtom(value)
  return atomic
}

/** Compares the atom classifier with Lean's `Types.Atoms.classify`. */
export async function checkAtomsRuntime(oracle: Oracle): Promise<void> {
  checkRealChains(tails)
  // 23 real chains behind zero to three custom prototypes.
  const rows = await oracleCorpus(oracle, 'Atoms', 92, 64 * 1024)
  let atoms = 0
  for (const line of rows) if (checkRow(jsonObject(JSON.parse(line)))) atoms += 1
  console.log(
    `Atoms Lean/native bridge: ${rows.length} prototype chains, ${atoms} atoms kept by snapshot, ` +
      'reconcile and produce and rejected by serialize',
  )
}
