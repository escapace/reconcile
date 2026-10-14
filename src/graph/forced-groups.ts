import type {
  ChoicePosition,
  Domains,
  ForcedGroup,
  ForcedGroups,
  Label,
  SupportGraph,
} from '../types'

/** Builds mandatory implications using every support in the complete target domain. */
export function supportGraph(domains: Domains): SupportGraph {
  const positions: ChoicePosition[] = []
  const supports = domains.map((domain, node) => {
    const unique = new Map<Label, number | null>()
    for (let choice = 0; choice < domain.length; choice += 1) {
      const identity = domain[choice].identity
      unique.set(identity, unique.has(identity) ? null : positions.length)
      positions.push({ choice, node })
    }
    return unique
  })
  const edges = positions.map(({ choice, node }) => {
    const targets: number[] = []
    for (const edge of domains[node][choice].required) {
      const target = supports[edge.node]?.get(edge.identity)
      if (target !== undefined && target !== null) targets.push(target)
    }
    return targets
  })
  return { edges, positions }
}

// Iterative depth-first search from each unseen root in order. `finish` receives every vertex
// it reaches once its edges are exhausted, with the root it was reached from.
function depthFirst(
  edges: ReadonlyArray<readonly number[]>,
  roots: Iterable<number>,
  seen: Uint8Array,
  finish: (vertex: number, root: number) => void,
): void {
  const next = new Array<number>(edges.length).fill(0)
  const stack: number[] = []
  for (const root of roots) {
    if (seen[root] !== 0) continue
    seen[root] = 1
    stack.push(root)
    while (stack.length !== 0) {
      const source = stack[stack.length - 1]
      const target = edges[source][next[source]++]
      if (target === undefined) {
        finish(source, root)
        stack.pop()
      } else if (seen[target] === 0) {
        seen[target] = 1
        stack.push(target)
      }
    }
  }
}

/**
 * Labels each strongly connected component by its smallest admitted vertex.
 *
 * @remarks
 * Iterative Kosaraju traversal uses bounded per-call state and linear graph work: the second
 * pass walks the reverse graph in reverse finishing order, and each root reaches exactly its
 * component. Edges must reference admitted dense vertices. FiniteReachability supplies the
 * independent executable reference used by the bridge; no native kind is inspected.
 */
export function componentLabels(edges: ReadonlyArray<readonly number[]>): number[] {
  const size = edges.length
  const reverse: number[][] = Array.from({ length: size }, () => [])
  for (let source = 0; source < size; source += 1)
    for (const target of edges[source]) reverse[target].push(source)
  const seen = new Uint8Array(size)
  const finished: number[] = []
  depthFirst(edges, edges.keys(), seen, (vertex) => finished.push(vertex))
  seen.fill(0)
  const labels = new Array<number>(size)
  depthFirst(reverse, finished.reverse(), seen, (vertex, root) => (labels[vertex] = root))
  // Ascending positions canonically name components without a comparison sort.
  const leaders = new Array<number>(size)
  for (let id = 0; id < size; id += 1) labels[id] = leaders[labels[id]] ??= id
  return labels
}

// Whether some requirement points at its own node or an earlier one.
function backward(domains: Domains): boolean {
  for (let node = 0; node < domains.length; node += 1)
    for (const choice of domains[node])
      for (const edge of choice.required) if (edge.node <= node) return true
  return false
}

/**
 * Compiles mutually forced choices into atomic decisions at their earliest owner.
 *
 * @remarks
 * Strictly forward requirements certify singleton components without graph allocation.
 * Otherwise every choice position participates in support discovery, including duplicate
 * identities. ForcedGroups proves component membership, conflict rejection, and exact
 * expansion; the iterator retains original score tiers and node order.
 */
export function forcedGroups(domains: Domains): ForcedGroups | undefined {
  if (!backward(domains)) return undefined
  const { edges, positions } = supportGraph(domains)
  const labels = componentLabels(edges)
  const members: ChoicePosition[][] = []
  for (let id = 0; id < positions.length; id += 1) (members[labels[id]] ??= []).push(positions[id])
  let result: Array<Array<ForcedGroup | null | undefined> | undefined> | undefined
  const owners = new Set<number>()
  const storage = new Set<Label>()
  for (const group of members) {
    if (group === undefined || group.length < 2) continue
    // A group is valid when every member has its own node and its own storage.
    let valid = true
    owners.clear()
    storage.clear()
    for (const position of group) {
      const choice = domains[position.node][position.choice]
      valid &&= !owners.has(position.node) && !storage.has(choice.storage)
      owners.add(position.node)
      storage.add(choice.storage)
    }
    const decision = valid ? group : null
    result ??= []
    for (const position of group) (result[position.node] ??= [])[position.choice] = decision
  }
  return result
}
