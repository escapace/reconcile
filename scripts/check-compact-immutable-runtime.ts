import assert from 'node:assert/strict'
import { oracleCorpus, type Oracle } from './lean-oracle'
import { compactFixture } from '../src/__tests__/fixtures/compact-immutable'
import type { CompactImmutableInput } from '../src/__tests__/fixtures/compact-immutable'
import { constructionOrder } from '../src/graph/construction'
import { immutableSelections } from '../src/graph/immutable-selection'

interface Observation {
  input: CompactImmutableInput
  masks: boolean[][]
  orders: Array<number[] | null>
}
interface Totals {
  plans: number
  /** Construction orders that are not ascending, since a dependency follows its dependent. */
  reordered: number
}

function checkRow(row: CompactImmutableInput['rows'][number], size: number, context: string) {
  assert.ok(Number.isSafeInteger(row.proposed) && row.proposed >= size, context)
  assert.ok(Number.isSafeInteger(row.storage) && row.storage >= size, context)
  assert.equal(typeof row.eligible, 'boolean', context)
  assert.equal(typeof row.fixed, 'boolean', context)
  assert.ok(
    row.children.every((child) => Number.isInteger(child) && child >= 0 && child < size),
    context,
  )
}

function checkInput(input: CompactImmutableInput, context: string): void {
  assert.ok(Array.isArray(input.rows) && input.rows.length <= 64, context)
  assert.equal(input.dependencies.length, input.rows.length, context)
  for (const row of input.rows) checkRow(row, input.rows.length, context)
  // Each record is its own storage, as compileImmutable registers each target once.
  assert.equal(new Set(input.rows.map((row) => row.storage)).size, input.rows.length, context)
}

/** Checks one case's native ranked stream and construction orders against Lean. The Lean masks
 * are the complete ranked stream of the case's domains. */
function checkCase(observation: Observation, context: string, totals: Totals): void {
  const { input, masks, orders } = observation
  checkInput(input, context)
  const actual = [...immutableSelections(compactFixture(input))]
  assert.deepEqual(actual, masks, context)
  const actualOrders = actual.map((mask) => constructionOrder(input.dependencies, mask))
  assert.deepEqual(actualOrders, orders, `${context}: construction order`)
  totals.plans += actual.length
  totals.reordered += actualOrders.filter((order) =>
    order.some((node, position) => position > 0 && node < order[position - 1]),
  ).length
}

/** Checks the actual compact iterator against Lean's full ranked streams and construction orders. */
export async function checkCompactImmutableRuntime(oracle: Oracle): Promise<void> {
  const lines = await oracleCorpus(oracle, 'CompactImmutable', 8195, 128 * 1024 * 1024)
  const totals: Totals = { plans: 0, reordered: 0 }
  for (const [index, line] of lines.entries())
    checkCase(JSON.parse(line) as Observation, `Compact immutable oracle case ${index}`, totals)
  assert.ok(totals.reordered > 0)
  console.log(
    `Compact immutable bridge: ${lines.length} cases, ${totals.plans} ranked plans, ` +
      `${totals.reordered} reordered construction orders.`,
  )
}
