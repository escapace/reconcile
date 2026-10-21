import assert from 'node:assert/strict'
import { integerIn, jsonObject, oracleCorpus, type Oracle } from './lean-oracle'
import { produce } from '../src/produce'

/** `DraftIterationOracle` steps on a Map draft; an iteration returns the entries it walked. */
const steps: ReadonlyArray<(map: Map<number, number>) => Array<[number, number]> | undefined> = [
  (map) => [...map],
  (map) => void map.set(1, 10),
  (map) => void map.set(1, 11),
  (map) => void map.set(3, 30),
  (map) => void map.delete(2),
  (map) => void map.delete(9),
]

/** Runs one Lean script in a recipe and compares the walks, the result and its identity. */
function checkRow(row: Record<string, unknown>): void {
  const script = (row.steps as unknown[]).map((step) => integerIn(step, 0, steps.length - 1))
  const base = new Map([
    [1, 10],
    [2, 20],
  ])
  const iterations: Array<Array<[number, number]>> = []
  const result = produce({ map: base }, (draft) => {
    for (const step of script) {
      const walked = steps[step](draft.map)
      if (walked !== undefined) iterations.push(walked)
    }
    return draft
  })
  const label = JSON.stringify(row)
  assert.deepEqual(iterations, row.iterations, `iterations ${label}`)
  assert.deepEqual([...result.map], row.entries, `entries ${label}`)
  assert.equal(result.map === base, row.kept, `kept ${label}`)
  assert.deepEqual(
    [...base],
    [
      [1, 10],
      [2, 20],
    ],
  )
}

/** Compares Map draft iteration with Lean's `DraftIteration`. */
export async function checkDraftIterationRuntime(oracle: Oracle): Promise<void> {
  // Every script of one to three of six steps: 6 + 36 + 216.
  const rows = await oracleCorpus(oracle, 'DraftIteration', 258, 256 * 1024)
  for (const line of rows) checkRow(jsonObject(JSON.parse(line)))
  console.log(
    `Draft-iteration Lean/native bridge: ${rows.length} scripts of iterations and writes walk, ` +
      'change and keep the Map as Lean does',
  )
}
