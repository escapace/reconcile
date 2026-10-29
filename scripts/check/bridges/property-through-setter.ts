import assert from 'node:assert/strict'
import { integerIn, jsonObject, oracleCorpus, type Oracle } from '../oracle'
import { produce } from '../../../src/produce'

type Row = Record<string, unknown>

const KEY = 'key'
const ASSIGNED = 9

/** A prototype whose setter for the key defines what the row says on its receiver, or nothing. */
function prototypeFor(row: Row): object {
  const defines =
    row.defines === 'data'
      ? (receiver: object) =>
          Object.defineProperty(receiver, KEY, {
            configurable: row.configurable === true,
            enumerable: row.enumerable === true,
            value: integerIn(row.value, 0, 1),
            writable: row.writable === true,
          })
      : () => undefined
  return Object.defineProperty({}, KEY, {
    configurable: true,
    get: () => 7,
    set(this: object) {
      defines(this)
    },
  })
}

function instance(row: Row): Record<string, unknown> {
  const object = Object.create(prototypeFor(row)) as Record<string, unknown>
  if (row.extensible !== true) Object.preventExtensions(object)
  return object
}

/** Describes an own property the way the oracle encodes it. */
function describe(target: object): Row {
  const descriptor = Object.getOwnPropertyDescriptor(target, KEY)
  if (descriptor === undefined) return { kind: 'none' }
  assert.ok('value' in descriptor)
  return {
    configurable: descriptor.configurable,
    enumerable: descriptor.enumerable,
    kind: 'data',
    value: descriptor.value,
    writable: descriptor.writable,
  }
}

function expected(descriptor: Row): Row {
  const { configurable, enumerable, kind, value, writable } = descriptor
  return kind === 'none' ? { kind } : { configurable, enumerable, kind, value, writable }
}

/** Assignment on an ordinary object, in strict code, where a failed definition throws. */
function onObject(row: Row): { after: Row; ok: boolean } {
  const object = instance(row)
  try {
    object[KEY] = ASSIGNED
  } catch (error) {
    assert.ok(error instanceof TypeError, String(error))
    return { after: describe(object), ok: false }
  }
  return { after: describe(object), ok: true }
}

/** The same assignment in a `produce` recipe; a refused definition throws out of `produce`. */
function onDraft(row: Row): { after: Row; ok: boolean } {
  const base = instance(row)
  let result: object
  try {
    result = produce(base, (draft) => {
      draft[KEY] = ASSIGNED
      return draft
    })
  } catch {
    return { after: describe(base), ok: false }
  }
  return { after: describe(result), ok: true }
}

function checkRow(row: Row): void {
  const object = onObject(row)
  assert.equal(object.ok, row.objectOk, 'object status')
  assert.deepEqual(object.after, expected(jsonObject(row.objectAfter)), 'object descriptor')
  const draft = onDraft(row)
  assert.equal(draft.ok, row.ok, `draft status: ${JSON.stringify(row)}`)
  assert.deepEqual(draft.after, expected(jsonObject(row.after)), 'draft descriptor')
}

/** Compares a recipe's assignment through an inherited setter with Lean's `draftThroughSetter`,
 * and the same assignment on an ordinary object with `throughSetter`. */
export async function checkPropertyThroughSetterRuntime(oracle: Oracle): Promise<void> {
  // A setter defining nothing, or the key with each of 8 attribute sets and 2 values, on an
  // extensible and a non-extensible object.
  const rows = (await oracleCorpus(oracle, 'PropertyThroughSetter', 34, 64 * 1024)).map((line) =>
    jsonObject(JSON.parse(line)),
  )
  for (const row of rows) checkRow(row)
  const same = rows.filter((row) => row.ok === row.objectOk).length
  console.log(
    `Property-through-setter Lean/native bridge: ${rows.length} assignments on objects and ` +
      `produce drafts; ${same} where the draft behaves as the object`,
  )
}
