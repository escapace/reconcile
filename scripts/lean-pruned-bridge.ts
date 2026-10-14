// Differential fixtures for identical-occupant pruning. The oracle publishes the captured
// records over the current heap with pinned nodes fixed; the runtime reconciles the same
// graph and reports identities, values and edges at the paths of the next graph.
import assert from 'node:assert/strict'
import type { Oracle } from './lean-oracle'
import { reconcile } from '../src/reconcile'
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
  before: number[]
  children: number[][]
  name: string
  nodes: NextNode[]
}
interface NextNode {
  children?: number[]
  occupant?: number
  pinned?: number
  shared?: number
  value?: number
}

/** The children of a fresh next node; pinned and shared nodes are current nodes as they are. */
function nextChildren(node: NextNode): readonly number[] {
  return node.pinned !== undefined || node.shared !== undefined ? [] : (node.children ?? [])
}

function freshNode(name: string, node: NextNode, index: number): GraphNode {
  assert.ok(index === 0 || node.occupant !== 0, `${name}: root occupant reused`)
  return { value: node.value ?? 0 }
}

function nextGraph(fixture: Fixture, current: GraphNode[]): GraphNode[] {
  const next = fixture.nodes.map((node, index) => {
    const placed = node.pinned ?? node.shared
    return placed === undefined ? freshNode(fixture.name, node, index) : current[placed]
  })
  linkChildren(next, (id) => nextChildren(fixture.nodes[id]))
  return next
}

function checkPinned(fixture: Fixture, current: GraphNode[], result: GraphNode[]): void {
  for (const [id, node] of fixture.nodes.entries())
    if (node.pinned !== undefined) {
      assert.equal(result[id], current[node.pinned], `${fixture.name}: pinned moved`)
      assert.equal(current[node.pinned].value, fixture.before[node.pinned])
    }
}

function observePruned(fixture: Fixture): GraphObservation {
  const size = fixture.before.length
  assert.ok(size > 0 && fixture.children.length === size && fixture.nodes.length > 0)
  const current: GraphNode[] = fixture.before.map((value) => ({ value }))
  linkChildren(current, (id) => fixture.children[id])
  const next = nextGraph(fixture, current)
  // Ground every next node at an actual path from the root of the next graph.
  const paths = groundPaths((id) => nextChildren(fixture.nodes[id]))
  assert.equal(paths.size, fixture.nodes.length, `${fixture.name}: unreachable next node`)
  const result = reconcile(current[0], next[0])
  assert.equal(result, current[0], `${fixture.name}: root identity changed`)
  const resultNodes = fixture.nodes.map((_, id) => nodeAt(result, paths.get(id)!))
  const identity = identityLabels(current, resultNodes, 2 * size, fixture.name)
  checkPinned(fixture, current, resultNodes)
  return observeGraph(fixture.name, resultNodes, identity, (node) =>
    Object.keys(node)
      .filter((key) => key.startsWith('child'))
      .map((key) => identity(node[key] as GraphNode)),
  )
}

export async function checkPrunedRuntime(oracle: Oracle): Promise<void> {
  await checkGraphFixtures(oracle, 'Pruned', 'lean/pruned-fixtures.json', 'pruned', observePruned)
}
