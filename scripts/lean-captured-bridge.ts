// Differential fixtures for the captured immutable core. Recipe/proxy semantics remain
// runtime-tested boundaries; this checks graph values, aliases and reuse. Each fixture is a
// numbered graph whose edges are `child<slot>` properties, grounded at a path from the root and
// reported in the vocabulary of the Lean contract oracle.
import assert from 'node:assert/strict'
import { readFileSync } from 'node:fs'
import type { Oracle } from './lean-oracle'
import { produce } from '../src/produce'

interface GraphNode {
  [key: string]: number | GraphNode
  value: number
}

interface GraphObservation {
  edges: number[][]
  identities: number[]
  values: number[]
}

interface Fixture {
  after: number[]
  before: number[]
  children: number[][]
  name: string
  undo: boolean
}

const FIXTURES = 'lean/fixtures/reuse-fixtures.json'

/** The input graph: slot `i` of node `id` points at node `children[id][i]`. */
function inputGraph(fixture: Fixture): GraphNode[] {
  const size = fixture.before.length
  const current: GraphNode[] = fixture.before.map((value) => ({ value }))
  assert.ok(fixture.children.flat().every((child) => child >= 0 && child < size))
  current.forEach((node, id) =>
    fixture.children[id].forEach((child, slot) => {
      node[`child${slot}`] = current[child]
    }),
  )
  return current
}

/** Breadth-first child-slot paths from node 0 to every reachable node. */
function groundPaths(children: readonly number[][]): Map<number, string[]> {
  const paths = new Map<number, string[]>([[0, []]])
  const pending = [0]
  for (const id of pending)
    children[id].forEach((child, slot) => {
      if (paths.has(child)) return
      paths.set(child, [...paths.get(id)!, `child${slot}`])
      pending.push(child)
    })
  return paths
}

/** Writes the fixture's final value, through an undone intermediate write when requested. */
function rewrite(fixture: Fixture, id: number, node: () => GraphNode): void {
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
  const paths = groundPaths(fixture.children)
  assert.equal(paths.size, size, `${fixture.name}: unreachable fixture node`)
  const at = (root: GraphNode, id: number): GraphNode =>
    paths.get(id)!.reduce((node, key) => node[key] as GraphNode, root)
  const result = produce(current[0], (draft) => {
    for (let id = 0; id < size; id += 1) rewrite(fixture, id, () => at(draft, id))
    return draft
  })
  const resultNodes = fixture.before.map((_, id) => at(result, id))
  // Distinct nodes stay distinct objects.
  resultNodes.forEach((node, id) => {
    assert.equal(resultNodes.indexOf(node), id, `${fixture.name}: distinct nodes collapsed`)
  })
  // A kept node is labelled by its input index, a new one by the node count plus its index.
  const identity = (node: GraphNode): number => {
    const old = current.indexOf(node)
    if (old >= 0) return old
    const fresh = resultNodes.indexOf(node)
    assert.ok(fresh >= 0, `${fixture.name}: unexpected result identity`)
    return size + fresh
  }
  checkInputKept(fixture, current, resultNodes)
  return {
    edges: resultNodes.map((node, id) =>
      fixture.children[id].map((_, slot) => identity(node[`child${slot}`] as GraphNode)),
    ),
    identities: resultNodes.map(identity),
    values: resultNodes.map((node) => node.value),
  }
}

export async function checkCapturedRuntime(oracle: Oracle): Promise<void> {
  const fixtures = JSON.parse(readFileSync(FIXTURES, 'utf8')) as Fixture[]
  const expected = JSON.parse(
    await oracle('Contract', { input: JSON.stringify(fixtures) }),
  ) as GraphObservation[]
  assert.deepEqual(fixtures.map(observeCaptured), expected)
  console.log(`Lean/runtime agreement: ${fixtures.length} captured graph fixtures passed.`)
}
