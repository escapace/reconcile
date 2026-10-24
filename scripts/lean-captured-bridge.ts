// Differential fixtures for the captured immutable core. Recipe/proxy semantics
// remain runtime-tested boundaries; this checks graph values, aliases and reuse.
import assert from 'node:assert/strict'
import type { Oracle } from './lean-oracle'
import { produce } from '../src/produce'
import {
  checkGraphFixtures,
  groundPaths,
  identityLabels,
  linkChildren,
  nodeAt,
  observeGraph,
  type GraphNode,
  type GraphObservation,
} from './lean-graph-fixtures'

interface Fixture {
  after: number[]
  before: number[]
  children: number[][]
  name: string
  undo: boolean
  untouched?: boolean[]
}

/** The input graph. */
function inputGraph(fixture: Fixture): GraphNode[] {
  const size = fixture.before.length
  const current: GraphNode[] = fixture.before.map((value) => ({ value }))
  assert.ok(fixture.children.flat().every((child) => child >= 0 && child < size))
  linkChildren(current, (id) => fixture.children[id])
  return current
}

/** Writes the fixture's final value, through an undone intermediate write when requested. */
function rewrite(fixture: Fixture, id: number, node: () => GraphNode): void {
  if (fixture.untouched?.[id] === true) {
    assert.equal(fixture.after[id], fixture.before[id])
    return
  }
  const target = node()
  if (fixture.undo) target.value = fixture.after[id] + 1
  target.value = fixture.after[id]
}

function checkInputKept(fixture: Fixture, current: GraphNode[], result: GraphNode[]): void {
  fixture.children.forEach((children, id) => {
    assert.equal(current[id].value, fixture.before[id], `${fixture.name}: input was mutated`)
    children.forEach((child, slot) => {
      assert.equal(current[id][`child${slot}`], current[child])
      assert.equal(result[id][`child${slot}`], result[child])
    })
  })
}

function observeCaptured(fixture: Fixture): GraphObservation {
  const size = fixture.before.length
  assert.ok(size > 0 && fixture.after.length === size && fixture.children.length === size)
  const current = inputGraph(fixture)
  // Ground every fixture node at an actual path from the public root.
  const paths = groundPaths((id) => fixture.children[id])
  assert.equal(paths.size, size, `${fixture.name}: unreachable fixture node`)
  const at = (root: GraphNode, id: number): GraphNode => nodeAt(root, paths.get(id)!)
  const result = produce(current[0], (draft) => {
    for (let id = 0; id < size; id += 1) rewrite(fixture, id, () => at(draft, id))
    return draft
  })
  const resultNodes = fixture.before.map((_, id) => at(result, id))
  // Distinct nodes stay distinct objects.
  resultNodes.forEach((node, id) => {
    assert.equal(resultNodes.indexOf(node), id, `${fixture.name}: distinct nodes collapsed`)
  })
  const identity = identityLabels(current, resultNodes, size, fixture.name)
  checkInputKept(fixture, current, resultNodes)
  return observeGraph(fixture.name, resultNodes, identity, (node, id) =>
    fixture.children[id].map((_, slot) => identity(node[`child${slot}`] as GraphNode)),
  )
}

export async function checkCapturedRuntime(oracle: Oracle): Promise<void> {
  await checkGraphFixtures(
    oracle,
    'Contract',
    'lean/fixtures/reuse-fixtures.json',
    'captured',
    observeCaptured,
  )
}
