import assert from 'node:assert/strict'
import type { Oracle } from './lean-oracle'
import { compactFixture } from '../src/__tests__/fixtures/compact-immutable'
import type { CompactImmutableInput } from '../src/__tests__/fixtures/compact-immutable'
import { constructionOrder } from '../src/graph/construction'
import { immutableSelections } from '../src/graph/immutable-selection'
import type { Domains } from '../src/types'

interface Observation {
  domains: Domains
  input: CompactImmutableInput
  masks: boolean[][]
  orders: Array<number[] | null>
  ownerBound: number
  selected: boolean[] | null
}
interface Totals {
  inhabited: number
  plans: number
  rejectedConstruction: number
  strictOwnerBounds: number
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
}

/** Checks one case's native ranked stream, owner bound and construction orders against Lean. The
 * Lean masks are the complete ranked stream of the case's domains. */
function checkCase(observation: Observation, context: string, totals: Totals): void {
  const { input, masks, orders, selected } = observation
  checkInput(input, context)
  const problem = compactFixture(input)
  const owners = new Set(problem.storages.filter((_, node) => !problem.unavailable.has(node)))
  assert.equal(owners.size, observation.ownerBound, `${context}: native owner labels`)
  const actual = [...immutableSelections(problem)]
  totals.strictOwnerBounds += Number(
    actual.length !== 0 && input.rows.filter((row) => row.eligible).length > owners.size,
  )
  assert.deepEqual(actual, masks, context)
  const actualOrders = actual.map((mask) => constructionOrder(input.dependencies, mask) ?? null)
  assert.deepEqual(actualOrders, orders, `${context}: construction order`)
  const first = actual.find((_, plan) => actualOrders[plan] !== null) ?? null
  assert.deepEqual(first, selected, `${context}: first construction-valid mask`)
  totals.plans += actual.length
  totals.inhabited += Number(first !== null)
  totals.rejectedConstruction += actualOrders.filter((order) => order === null).length
}

/** Checks the actual compact iterator against Lean's full ranked streams and construction results. */
export async function checkCompactImmutableRuntime(oracle: Oracle): Promise<void> {
  const output = await oracle('CompactImmutable', [], { maxBuffer: 128 * 1024 * 1024 })
  const lines = output.trimEnd().split('\n')
  const count = Number(lines.shift())
  assert.ok(Number.isSafeInteger(count) && count > 0, 'Invalid compact oracle case count')
  assert.equal(lines.length, count)
  const totals: Totals = { inhabited: 0, plans: 0, rejectedConstruction: 0, strictOwnerBounds: 0 }
  for (const [index, line] of lines.entries())
    checkCase(JSON.parse(line) as Observation, `Compact immutable oracle case ${index}`, totals)
  assert.ok(totals.inhabited > 0 && totals.inhabited < count)
  assert.ok(totals.rejectedConstruction > 0)
  assert.ok(totals.strictOwnerBounds > 0)
  console.log(
    `Compact immutable bridge: ${count} cases, ${totals.plans} ranked plans, ${totals.inhabited} inhabited, ` +
      `${totals.rejectedConstruction} construction rejections, ${totals.strictOwnerBounds} strict owner bounds.`,
  )
}
