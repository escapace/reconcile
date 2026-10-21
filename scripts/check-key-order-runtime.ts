import assert from 'node:assert/strict'
import { integerIn, jsonObject, oracleCorpus, type Oracle } from './lean-oracle'
import { decodeKey } from './property-bridge-fixtures'
import { produce } from '../src/produce'

const symbols = [Symbol('first')]

/** Decodes a Lean key code; labels run to 1: two integer keys, two names and one symbol. */
function key(code: unknown): PropertyKey {
  return decodeKey(code, 5, symbols)
}

function list(value: unknown): unknown[] {
  assert.ok(Array.isArray(value))
  return value
}

type Mutation = (target: Record<PropertyKey, unknown>) => void

/** An assignment is `2 * code`, a deletion `2 * code + 1`. */
function mutation(code: unknown): Mutation {
  const value = integerIn(code, 0, 11)
  const property = key(Math.floor(value / 2))
  return value % 2 === 0
    ? (target) => {
        target[property] = 1
      }
    : (target) => {
        delete target[property]
      }
}

/** An ordinary object created by assigning keys in order. */
function create(created: readonly PropertyKey[]): Record<PropertyKey, unknown> {
  const target: Record<PropertyKey, unknown> = {}
  for (const property of created) target[property] = 0
  return target
}

/** Compares the engine and `produce` with Lean's own keys for one case. */
function checkCase(row: Record<string, unknown>): void {
  const created = list(row.created).map(key)
  const mutations = list(row.ops).map(mutation)
  const expected = list(row.own).map(key)
  const plain = create(created)
  for (const apply of mutations) apply(plain)
  assert.deepEqual(Reflect.ownKeys(plain), expected, 'engine own keys')
  const result = produce(create(created), (draft) => {
    for (const apply of mutations) apply(draft)
    return draft
  })
  assert.deepEqual(Reflect.ownKeys(result), expected, 'produce own keys')
}

/** Compares the engine's own-key order and `produce`'s result order with Lean's `ownKeys`. */
export async function checkKeyOrderRuntime(oracle: Oracle): Promise<void> {
  // 326 creation orders of up to five keys × 111 sequences of up to two mutations.
  const rows = await oracleCorpus(oracle, 'KeyOrder', 36_186, 8 * 1024 * 1024)
  for (const line of rows) checkCase(jsonObject(JSON.parse(line)))
  console.log(
    `Key-order Lean/native bridge: ${rows.length} mutation sequences; the engine and produce ` +
      'match Lean own keys',
  )
}
