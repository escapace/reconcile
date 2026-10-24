import assert from 'node:assert/strict'
import { jsonObject, oracleCorpus, type Oracle } from './lean-oracle'
import { produce } from '../src/produce'

const searches = ['includes', 'indexOf', 'lastIndexOf'] as const

/** The scenarios of `DraftMembersOracle`: the array draft each searches. */
const scenarios = ['plain', 'plain, searched first'] as const

/** The objects `a` and `b` and the state whose array draft a scenario searches. */
function scenarioState() {
  const a = { name: 'a' }
  const b = { name: 'b' }
  const list: unknown[] = [a, b, a, 7]
  return { a, b, state: { list } }
}

/** One search of the array draft of `scenario` for the form `query` names. In the searched-first
 * scenario each search runs in a recipe of its own, which reads no element before it except to
 * get a draft form; otherwise the recipe reads the first element first and then the second. */
function search(scenario: string, query: string, method: (typeof searches)[number]): unknown {
  const { a, b, state } = scenarioState()
  const fresh = scenario === 'plain, searched first'
  const readFirst = !fresh || query === 'a draft'
  const readSecond = !fresh || query === 'b draft'
  return produce(state, (draft) => {
    const first = readFirst ? draft.list[0] : a
    const second = readSecond ? draft.list[1] : b
    const forms: Record<string, unknown> = {
      '7': 7,
      '8': 8,
      a,
      'a draft': first,
      b,
      'b draft': second,
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
  // Seven searched values in each of two scenarios: two forms of one object, two of another,
  // another object and two numbers.
  const rows = (await oracleCorpus(oracle, 'DraftMembers', 14, 64 * 1024)).map((line) =>
    jsonObject(JSON.parse(line)),
  )
  let checked = 0
  for (const scenario of scenarios) checked += checkArray(rows, scenario)
  console.log(
    `Draft-members Lean/native bridge: ${checked} searches of array drafts find an object in ` +
      'any of its forms where Lean does',
  )
}
