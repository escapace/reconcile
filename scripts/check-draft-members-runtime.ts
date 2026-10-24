import assert from 'node:assert/strict'
import { reactive, shallowReactive } from 'vue'
import { jsonObject, oracleCorpus, type Oracle } from './lean-oracle'
import { produce } from '../src/produce'

const searches = ['includes', 'indexOf', 'lastIndexOf'] as const

/** The scenarios of `DraftMembersOracle`: the array draft each searches. */
const scenarios = ['plain', 'plain, proxy drafted first', 'plain, searched first', 'vue'] as const

/** The objects `a` and `b` and the state whose array draft `scenario` searches. */
function scenarioState(scenario: string) {
  const a = { name: 'a' }
  const b = { name: 'b' }
  const vue = scenario === 'vue'
  const list: unknown[] = [scenario === 'plain' || vue ? a : reactive(a), b, a, 7]
  return { a, b, state: vue ? reactive({ list }) : { list } }
}

/** One search of the array draft of `scenario` for the form `query` names. In the searched-first
 * scenario each search runs in a recipe of its own, which reads no element before it except to
 * get a draft form; otherwise the recipe reads the first element first and then the second. */
function search(scenario: string, query: string, method: (typeof searches)[number]): unknown {
  const { a, b, state } = scenarioState(scenario)
  const fresh = scenario === 'plain, searched first'
  const readFirst = !fresh || query === 'a draft'
  const readSecond = !fresh || query === 'b draft'
  return produce(state, (draft) => {
    const first = readFirst ? draft.list[0] : a
    const second = readSecond ? draft.list[1] : b
    // A Vue proxy of an element is what the reactive state hands out; a plain array holds the
    // element itself, and its proxy is one of its own.
    const forms: Record<string, unknown> = {
      '7': 7,
      '8': 8,
      a,
      'a draft': first,
      'a proxy': reactive(a),
      'a shallow proxy': shallowReactive(a),
      b,
      'b draft': second,
      'b proxy': reactive(b),
      'other': { name: 'a' },
    }
    return (draft.list[method] as (value: unknown) => unknown)(forms[query])
  })
}

/** Searches the array draft of `scenario` for each form of each value in `DraftMembersOracle` and
 * compares the results with Lean's. */
function checkArray(rows: ReadonlyArray<Record<string, unknown>>, scenario: string): number {
  let checked = 0
  for (const row of rows) {
    if (row.scenario !== scenario) continue
    for (const method of searches) {
      const found = search(scenario, String(row.query), method)
      assert.deepEqual(found, row[method], `${scenario} ${method}(${String(row.query)})`)
      checked += 1
    }
  }
  return checked
}

/** Compares array draft searches with Lean's `DraftMembers`. */
export async function checkDraftMembersRuntime(oracle: Oracle): Promise<void> {
  // Ten searched values in each of four scenarios: four forms of one object, three of another,
  // another object and two numbers.
  const rows = (await oracleCorpus(oracle, 'DraftMembers', 40, 64 * 1024)).map((line) =>
    jsonObject(JSON.parse(line)),
  )
  let checked = 0
  for (const scenario of scenarios) checked += checkArray(rows, scenario)
  console.log(
    `Draft-members Lean/native bridge: ${checked} searches of plain and Vue reactive array ` +
      'drafts find an object in any of its forms where Lean does',
  )
}
