import assert from 'node:assert/strict'
import { reactive } from 'vue'
import { jsonObject, oracleCorpus, type Oracle } from './lean-oracle'
import { produce } from '../src/produce'

const searches = ['includes', 'indexOf', 'lastIndexOf'] as const

/** Searches the array draft `[a, b, a, 7]`, plain or Vue reactive, for each form of each value in
 * `DraftMembersOracle` and compares the results with Lean's. */
function checkArray(rows: ReadonlyArray<Record<string, unknown>>, vue: boolean): number {
  const a = { name: 'a' }
  const b = { name: 'b' }
  const state = vue
    ? reactive({ list: [a, b, a, 7] as unknown[] })
    : { list: [a, b, a, 7] as unknown[] }
  let checked = 0
  produce(state, (draft) => {
    // A Vue proxy of an element is what the reactive state hands out; a plain array has none.
    const forms: Record<string, unknown> = {
      '7': 7,
      '8': 8,
      a,
      'a draft': draft.list[0],
      'a proxy': state.list[0],
      b,
      'b draft': draft.list[1],
      'b proxy': state.list[1],
      'other': { name: 'a' },
    }
    for (const row of rows) {
      const value = forms[String(row.query)]
      for (const search of searches) {
        const found = (draft.list[search] as (value: unknown) => unknown)(value)
        assert.deepEqual(
          found,
          row[search],
          `${vue ? 'vue' : 'plain'} ${search}(${String(row.query)})`,
        )
        checked += 1
      }
    }
    return draft
  })
  return checked
}

/** Compares array draft searches with Lean's `DraftMembers`. */
export async function checkDraftMembersRuntime(oracle: Oracle): Promise<void> {
  // Nine searched values: three forms of each of two objects, another object and two numbers.
  const rows = (await oracleCorpus(oracle, 'DraftMembers', 9, 64 * 1024)).map((line) =>
    jsonObject(JSON.parse(line)),
  )
  const checked = checkArray(rows, false) + checkArray(rows, true)
  console.log(
    `Draft-members Lean/native bridge: ${checked} searches of plain and Vue reactive array ` +
      'drafts find an object in any of its forms where Lean does',
  )
}
