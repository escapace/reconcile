import assert from 'node:assert/strict'
import { reactive, shallowReactive } from 'vue'
import { jsonObject, oracleCorpus, type Oracle } from './lean-oracle'
import { produce } from '../src/produce'

const searches = ['includes', 'indexOf', 'lastIndexOf'] as const

/** The scenarios of `DraftMembersOracle`: the array draft each searches. */
const scenarios = ['plain', 'plain, proxy drafted first', 'vue'] as const

/** Searches the array draft of `scenario` for each form of each value in `DraftMembersOracle` and
 * compares the results with Lean's. */
function checkArray(rows: ReadonlyArray<Record<string, unknown>>, scenario: string): number {
  const a = { name: 'a' }
  const b = { name: 'b' }
  const vue = scenario === 'vue'
  const list: unknown[] = [scenario === 'plain' || vue ? a : reactive(a), b, a, 7]
  const state = vue ? reactive({ list }) : { list }
  let checked = 0
  produce(state, (draft) => {
    // Reading the first element before any other drafts it first; in the proxy-first scenario that
    // is `reactive(a)`, whose draft `a` then shares. A Vue proxy of an element is what the reactive
    // state hands out; a plain array holds the element itself, and its proxy is one of its own.
    const first = draft.list[0]
    const forms: Record<string, unknown> = {
      '7': 7,
      '8': 8,
      a,
      'a draft': first,
      'a proxy': reactive(a),
      'a shallow proxy': shallowReactive(a),
      b,
      'b draft': draft.list[1],
      'b proxy': reactive(b),
      'other': { name: 'a' },
    }
    for (const row of rows) {
      if (row.scenario !== scenario) continue
      const value = forms[String(row.query)]
      for (const search of searches) {
        const found = (draft.list[search] as (value: unknown) => unknown)(value)
        assert.deepEqual(found, row[search], `${scenario} ${search}(${String(row.query)})`)
        checked += 1
      }
    }
    return draft
  })
  return checked
}

/** Compares array draft searches with Lean's `DraftMembers`. */
export async function checkDraftMembersRuntime(oracle: Oracle): Promise<void> {
  // Ten searched values in each of three scenarios: four forms of one object, three of another,
  // another object and two numbers.
  const rows = (await oracleCorpus(oracle, 'DraftMembers', 30, 64 * 1024)).map((line) =>
    jsonObject(JSON.parse(line)),
  )
  let checked = 0
  for (const scenario of scenarios) checked += checkArray(rows, scenario)
  console.log(
    `Draft-members Lean/native bridge: ${checked} searches of plain and Vue reactive array ` +
      'drafts find an object in any of its forms where Lean does',
  )
}
