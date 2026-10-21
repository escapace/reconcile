import assert from 'node:assert/strict'
import { integerIn, jsonObject, oracleCorpus, type Oracle } from './lean-oracle'
import { produce } from '../src/produce'

type Row = Record<string, unknown>

/** `DraftSurfaceOracle` kinds: a value to draft and a reader for the written key in the result. */
const kinds: ReadonlyArray<() => object> = [
  () => ({ a: 1 }),
  () => [1, 2],
  () => new Map([[1, 2]]),
  () => new Uint8Array(2),
  () => new Date(0),
]

/** `DraftSurfaceOracle` keys: an index, `length` and another name, with a value to write. */
const keys: ReadonlyArray<[PropertyKey, number]> = [
  ['0', 7],
  ['length', 2],
  ['extra', 7],
]

/** Writes one key on a draft; an admitted write must reach the result. */
function checkAdmission(row: Row): void {
  const value = kinds[integerIn(row.kind, 0, kinds.length - 1)]()
  const [key, written] = keys[integerIn(row.key, 0, keys.length - 1)]
  let accepted: boolean | undefined
  const result = produce({ value }, (draft) => {
    accepted = Reflect.set(draft.value, key, written)
    return draft
  })
  assert.equal(accepted, row.admits, `admission ${String(key)}`)
  if (accepted === true)
    assert.equal(Reflect.get(result.value, key), written, `result ${String(key)}`)
}

/** Builds an object whose getters return the listed values and reports whether produce keeps
 * it: a primitive, a kept child, a changed child or a draft handle of the kept child. */
function checkKeeping(row: Row): void {
  const returned = (row.returned as unknown[]).map((code) => integerIn(code, 0, 3))
  const kept = { n: 0 }
  const changed = { n: 0 }
  let draftOfKept: object | undefined
  const values = [() => 1, () => kept, () => changed, () => draftOfKept]
  const target: Record<string, unknown> = { a: 1 }
  returned.forEach((code, index) =>
    Object.defineProperty(target, `g${index}`, {
      configurable: true,
      enumerable: true,
      get: values[code],
    }),
  )
  const current = { changed, kept, target }
  const result = produce(current, (draft) => {
    draftOfKept = draft.kept
    if (row.dataChanged === true) draft.target.a = 2
    draft.changed.n = 1
    return draft
  })
  assert.equal(result.target === target, row.keeps, `keeps ${JSON.stringify(row)}`)
  if (row.keeps !== true)
    for (const [index, code] of returned.entries()) {
      // A rebuilt object holds each returned value as data, a handle as the kept child.
      const expected = [1, kept, result.changed, kept][code]
      assert.equal(Object.getOwnPropertyDescriptor(result.target, `g${index}`)?.value, expected)
    }
}

/** Compares draft admission and own-accessor reuse with Lean's `DraftSurface`. */
export async function checkDraftSurfaceRuntime(oracle: Oracle): Promise<void> {
  // 15 kind and key pairs, then 2 × 20 objects with one or two getters.
  const rows = await oracleCorpus(oracle, 'DraftSurface', 55, 64 * 1024)
  let admissions = 0
  for (const line of rows) {
    const row = jsonObject(JSON.parse(line))
    if ('admits' in row) {
      checkAdmission(row)
      admissions += 1
    } else checkKeeping(row)
  }
  console.log(
    `Draft-surface Lean/native bridge: ${admissions} draft writes admitted exactly where the ` +
      `result carries them; ${rows.length - admissions} getter objects kept exactly where Lean keeps them`,
  )
}
