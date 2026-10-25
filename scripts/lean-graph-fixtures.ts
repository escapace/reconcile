// Plumbing for the captured graph bridge: it builds numbered graphs whose edges are
// `child<slot>` properties, grounds every node at a path from the root and reports identities,
// values and edges in the vocabulary of the Lean contract oracle.
import assert from 'node:assert/strict'
import { readFileSync } from 'node:fs'
import type { Oracle } from './lean-oracle'

export interface GraphNode {
  [key: string]: number | GraphNode
  value: number
}
export interface GraphObservation {
  edges: number[][]
  identities: number[]
  name: string
  values: number[]
}

/** Points slot `i` of node `id` at node `children(id)[i]`. */
export function linkChildren(nodes: GraphNode[], children: (id: number) => readonly number[]) {
  nodes.forEach((node, id) =>
    children(id).forEach((child, slot) => {
      node[`child${slot}`] = nodes[child]
    }),
  )
}

/** Breadth-first child-slot paths from node 0 to every reachable node. */
export function groundPaths(children: (id: number) => readonly number[]): Map<number, string[]> {
  const paths = new Map<number, string[]>([[0, []]])
  const pending = [0]
  for (const id of pending)
    children(id).forEach((child, slot) => {
      if (paths.has(child)) return
      paths.set(child, [...paths.get(id)!, `child${slot}`])
      pending.push(child)
    })
  return paths
}

export function nodeAt(root: GraphNode, path: readonly string[]): GraphNode {
  return path.reduce((node, key) => node[key] as GraphNode, root)
}

/** Labels a result node by its input index, or `freshBase` plus its result index when new. */
export function identityLabels(
  current: readonly GraphNode[],
  result: readonly GraphNode[],
  freshBase: number,
  name: string,
): (node: GraphNode) => number {
  return (node) => {
    const old = current.indexOf(node)
    if (old >= 0) return old
    const fresh = result.indexOf(node)
    assert.ok(fresh >= 0, `${name}: unexpected result identity`)
    return freshBase + fresh
  }
}

export function observeGraph(
  name: string,
  nodes: readonly GraphNode[],
  identity: (node: GraphNode) => number,
  edges: (node: GraphNode, id: number) => number[],
): GraphObservation {
  return {
    edges: nodes.map(edges),
    identities: nodes.map(identity),
    name,
    values: nodes.map((node) => node.value),
  }
}

/** Runs every fixture of `path` through the runtime and compares with the oracle's observations. */
export async function checkGraphFixtures<Fixture>(
  oracle: Oracle,
  family: string,
  path: string,
  label: string,
  observe: (fixture: Fixture) => GraphObservation,
): Promise<void> {
  const fixtures = JSON.parse(readFileSync(path, 'utf8')) as Fixture[]
  const expected = JSON.parse(await oracle(family, [path])) as GraphObservation[]
  assert.deepEqual(
    fixtures.map((fixture) => observe(fixture)),
    expected,
  )
  console.log(`Lean/runtime agreement: ${fixtures.length} ${label} graph fixtures passed.`)
}
