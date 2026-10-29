import assert from 'node:assert/strict'
import { integerIn, oracleCorpus, strictWitnesses, type Oracle } from '../oracle'
import { closeRequirements } from '../../../src/graph/requirements'

function facts(value: unknown, nodes: number, maximumLength: number): number[] {
  assert.ok(Array.isArray(value) && value.length <= maximumLength)
  return value.map((fact) => integerIn(fact, 0, nodes - 1))
}

/** Scans one closure trace performs over the given implication rows. */
function scans(trace: readonly number[], implications: readonly number[][]): number {
  return trace.reduce((sum, fact) => sum + implications[fact].length, 0)
}

/** Closes one seeded input over both rows; true when trimming saved strict work. */
function checkClosure(observation: Record<string, unknown>): boolean {
  assert.ok(Array.isArray(observation.parents) && observation.parents.length <= 64)
  const nodes = observation.parents.length
  const parents = observation.parents.map((row) => facts(row, nodes, 128))
  assert.ok(Array.isArray(observation.trimmed) && observation.trimmed.length === nodes)
  const trimmed = observation.trimmed.map((row) => facts(row, nodes, 128))
  const seeds = facts(observation.seeds, nodes, 64)
  const trace = facts(observation.trace, nodes, nodes)
  assert.equal(new Set(trace).size, trace.length)
  assert.deepEqual([...closeRequirements(seeds, parents)], trace)
  assert.deepEqual([...closeRequirements(seeds, trimmed)], trace)
  const oldScans = integerIn(
    observation.oldScans,
    0,
    parents.reduce((sum, row) => sum + row.length, 0),
  )
  const newScans = integerIn(observation.newScans, 0, oldScans)
  assert.equal(scans(trace, parents), oldScans)
  assert.equal(scans(trace, trimmed), newScans)
  return newScans < oldScans
}

/** Checks the shared native closure against Lean's original and trimmed finite inputs. */
export async function checkSeededRequirementsRuntime(oracle: Oracle): Promise<void> {
  const lines = await oracleCorpus(oracle, 'SeededRequirements', 40_966, 64 * 1024 * 1024)
  const strictSavings = strictWitnesses(lines, checkClosure)
  // Dropping a seed's outgoing row loses the late cyclic rejection.
  assert.deepEqual([...closeRequirements([0], [[1], [0]])], [0, 1])
  assert.deepEqual([...closeRequirements([0], [[], [0]])], [0])
  console.log(
    `Seeded-requirements Lean/native bridge: ${lines.length} traces; ${strictSavings} strict-work witnesses`,
  )
}
