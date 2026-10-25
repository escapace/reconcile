import type { Choice, Domains, ImmutableProblem } from '../../types'
import { isNode } from '../../graph/edge'

export interface CompactImmutableInput {
  readonly dependencies: number[][]
  readonly rows: Array<{
    children: number[]
    eligible: boolean
    fixed: boolean
    proposed: number
    storage: number
  }>
}

/** Supplies native objects for the finite oracle's identity and storage labels. */
export function compactFixture(input: CompactImmutableInput): ImmutableProblem {
  const objects = new Map<number, object>()
  const object = (label: number): object => {
    let value = objects.get(label)
    if (value === undefined) {
      value = { label }
      objects.set(label, value)
    }
    return value
  }
  const kind = Symbol('compact fixture')
  const records = input.rows.map((row) => {
    const edges = row.children.map((node) => ({ node }))
    return {
      edges,
      payload: row.fixed
        ? undefined
        : {
            attributes: undefined,
            edges,
            keys: [],
            layout: { kind },
            observed: undefined,
            pinned: undefined,
          },
      settled: undefined,
      target: object(row.proposed),
    }
  })
  return {
    conflict: false,
    records,
    root: 0,
    storages: input.rows.map((row) => object(row.storage)),
    unavailable: new Set(input.rows.flatMap((row, node) => (row.eligible ? [] : [node]))),
  }
}

/**
 * Every feasible selection of `domains` by descending retention and, within a score, in
 * lexicographic choice order: the reference order of a ranked stream, enumerated by a plain
 * backtracking search that keeps storages distinct and meets each requirement when the node it
 * names is chosen, before it through a demand.
 */
export function rankedSelections(domains: Domains): number[][] {
  const size = domains.length
  const all: Array<{ score: number; selection: number[] }> = []
  const selected: number[] = []
  const owners = new Set<unknown>()
  const demands = new Map<number, unknown>()
  // The identity selected or demanded at `node` so far, if any: a choice there must have it.
  const settled = (node: number, choice: Choice): unknown =>
    node < selected.length
      ? domains[node][selected[node]].identity
      : node === selected.length
        ? choice.identity
        : demands.get(node)
  const admits = (node: number, choice: Choice): boolean => {
    const demanded = demands.get(node)
    if (demanded !== undefined && demanded !== choice.identity) return false
    if (owners.has(choice.storage)) return false
    return choice.required.every((edge) => {
      const identity = settled(edge.node, choice)
      return identity === undefined || identity === edge.identity
    })
  }
  const visit = (node: number, score: number): void => {
    if (node === size) {
      all.push({ score, selection: selected.slice() })
      return
    }
    const domain = domains[node]
    for (let choice = 0; choice < domain.length; choice += 1) {
      const candidate = domain[choice]
      if (!admits(node, candidate)) continue
      const added: number[] = []
      for (const edge of candidate.required)
        if (edge.node > node && !demands.has(edge.node)) {
          demands.set(edge.node, edge.identity)
          added.push(edge.node)
        }
      owners.add(candidate.storage)
      selected.push(choice)
      visit(node + 1, score + Number(candidate.retained))
      selected.pop()
      owners.delete(candidate.storage)
      for (const edge of added) demands.delete(edge)
    }
  }
  visit(0, 0)
  return all
    .map((entry, index) => ({ ...entry, index }))
    .toSorted((left, right) =>
      right.score === left.score ? left.index - right.index : right.score - left.score,
    )
    .map((entry) => entry.selection)
}

/** Decodes compact native facts into the existing finite wire format without solving them. */
export function immutableDomains({ records, storages, unavailable }: ImmutableProblem): Domains {
  return records.map((record, node) => {
    const domain: Choice[] = []
    if (!unavailable.has(node)) {
      domain.push({
        identity: record.target,
        required: record.edges.flatMap((edge) =>
          isNode(edge) ? [{ identity: records[edge.node].target, node: edge.node }] : [],
        ),
        retained: true,
        storage: storages[node],
      })
    }
    if (record.payload !== undefined)
      domain.push({ identity: node, required: [], retained: false, storage: node })
    return domain
  })
}
