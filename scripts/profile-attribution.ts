import assert from 'node:assert/strict'

export interface AttributionFrame {
  readonly functionName: string
  readonly location: string
  readonly scope: 'mapped' | 'project' | 'unmapped'
}

export interface WeightedFrame extends AttributionFrame {
  inclusive: number
  self: number
}

export interface WeightedNode {
  readonly frame: AttributionFrame
  readonly id: number
  readonly weight: number
  readonly parent?: number
}

function aggregateOf(
  frames: Map<string, WeightedFrame>,
  key: string,
  frame: AttributionFrame,
): WeightedFrame {
  let aggregate = frames.get(key)
  if (aggregate === undefined) {
    aggregate = { ...frame, inclusive: 0, self: 0 }
    frames.set(key, aggregate)
  }
  return aggregate
}

/** Charges one node's weight to itself and once to each distinct source frame on its ancestry. */
function charge(
  node: WeightedNode,
  byId: ReadonlyMap<number, WeightedNode>,
  frames: Map<string, WeightedFrame>,
): void {
  const visited = new Set<number>()
  const sources = new Set<string>()
  let current: WeightedNode | undefined = node
  while (current !== undefined) {
    assert(!visited.has(current.id), 'Cyclic profile ancestry')
    visited.add(current.id)
    const { frame } = current
    const key = `${frame.scope}|${frame.functionName}|${frame.location}`
    const aggregate = aggregateOf(frames, key, frame)
    if (current === node) aggregate.self += node.weight
    if (!sources.has(key)) aggregate.inclusive += node.weight
    sources.add(key)
    const parent: number | undefined = current.parent
    current = parent === undefined ? undefined : byId.get(parent)
    assert(parent === undefined || current !== undefined, 'Missing profile parent')
  }
}

/** Attributes a sampled tree without counting a recursive source frame twice per sample. */
export function attribute(nodes: readonly WeightedNode[]) {
  const byId = new Map(nodes.map((node) => [node.id, node]))
  assert.equal(byId.size, nodes.length, 'Duplicate profile node IDs')
  const frames = new Map<string, WeightedFrame>()
  const coverage = { mapped: 0, project: 0, total: 0, unmapped: 0 }
  for (const node of nodes) {
    assert(Number.isFinite(node.weight) && node.weight >= 0, 'Invalid profile weight')
    coverage.total += node.weight
    coverage[node.frame.scope] += node.weight
    charge(node, byId, frames)
  }
  return { coverage, frames: [...frames.values()] }
}
