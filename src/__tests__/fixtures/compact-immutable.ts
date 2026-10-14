import type { Choice, Domains, ImmutableProblem } from '../../types'

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
      payload: row.fixed ? undefined : { edges, keys: [], layout: { kind } },
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

/** Decodes compact native facts into the existing finite wire format without solving them. */
export function immutableDomains({ records, storages, unavailable }: ImmutableProblem): Domains {
  return records.map((record, node) => {
    const domain: Choice[] = []
    if (!unavailable.has(node)) {
      domain.push({
        identity: record.target,
        required: record.edges.flatMap((edge) =>
          'node' in edge ? [{ identity: records[edge.node].target, node: edge.node }] : [],
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
