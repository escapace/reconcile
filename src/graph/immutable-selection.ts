import { isNode } from './edge'
import { finalizationChildInvalid, finalizationStorageMissing } from '../error'
import type { Edge, ImmutableProblem } from '../types'
import { denseArray } from '../standard-prototypes'

/**
 * Returns the mask keeping exactly the eligible records when it is admissible (every fixed record
 * is eligible), separated (eligible storages are distinct) and closed (every child of an eligible
 * record is eligible), and undefined otherwise. It is then the first mask `immutableSelections`
 * streams (CompactImmutable.ranked_head). Malformed input is left to the search, which reports it.
 */
export function immutableHead({
  records,
  storages,
  unavailable,
}: ImmutableProblem): boolean[] | undefined {
  const size = records.length
  const keep = denseArray<boolean>(size)
  for (let node = 0; node < size; node += 1) keep[node] = !unavailable.has(node)
  const owners = new Set<object>()
  for (let node = 0; node < size; node += 1) {
    if (!keep[node]) {
      if (records[node].payload === undefined) return undefined
      continue
    }
    const storage = storages[node] as object | undefined
    if (storage === undefined || owners.has(storage)) return undefined
    owners.add(storage)
    if (!childrenKept(records[node].edges, keep)) return undefined
  }
  return keep
}

// Whether every child edge names a valid kept record.
function childrenKept(edges: readonly Edge[], keep: readonly boolean[]): boolean {
  for (let index = 0; index < edges.length; index += 1) {
    const edge = edges[index]
    if (!isNode(edge)) continue
    const child = edge.node
    if (!Number.isInteger(child) || child < 0 || child >= keep.length || !keep[child]) return false
  }
  return true
}

/**
 * Streams immutable retained-node masks in descending score and keep-before-fresh order.
 *
 * @remarks
 * CompactImmutable proves decoding, complete ranked-stream equality and prefix pruning.
 * CompactOwners proves that distinct eligible owners bound every feasible retention score.
 * Every retained edge demands the child's sole proposed identity, so forward demands are
 * Boolean. Only newly installed demands enter the trail; undo preserves older demands.
 * Native compilation supplies all storage observations before this pure search begins.
 */
// fallow-ignore-next-line complexity -- per-step helper calls in this search slowed produce 1%
export function* immutableSelections({
  records,
  storages,
  unavailable,
}: ImmutableProblem): Generator<boolean[], void> {
  const size = records.length
  // Exact-size plain arrays; every slot is written before it is read.
  const maximum = denseArray<number>(size + 1)
  const minimum = denseArray<number>(size + 1)
  const retained = denseArray<boolean>(size)
  const needed = denseArray<boolean>(size)
  const eligibleNodes = denseArray<boolean>(size)
  maximum[size] = 0
  minimum[size] = 0
  const owners = new Set<object>()
  for (let node = size - 1; node >= 0; node -= 1) {
    retained[node] = false
    needed[node] = false
    const eligible = !unavailable.has(node)
    eligibleNodes[node] = eligible
    const fixed = records[node].payload === undefined
    if (fixed && !eligible) return
    if (eligible) {
      const storage = storages[node]
      if (storage === undefined) throw finalizationStorageMissing(node)
      owners.add(storage)
    }
    maximum[node] = maximum[node + 1] + Number(eligible)
    minimum[node] = minimum[node + 1] + Number(fixed)
  }
  const highest = owners.size
  // When eligible storages are pairwise distinct no kept path can repeat one, so the search
  // tracks owners only when some storage is shared (CompactOwners.separated_of_distinct).
  const shared = highest !== maximum[0]
  if (shared) owners.clear()
  const next = denseArray<number>(size)
  const checkpoints = denseArray<number>(size)
  const trail: number[] = []
  for (let goal = highest; goal >= minimum[0]; goal -= 1) {
    let node = 0
    let score = 0
    if (size !== 0) next[0] = 0
    while (node >= 0) {
      if (node === size) yield retained.slice()
      else {
        const attempt = next[node]++
        if (attempt < 2) {
          const keep = attempt === 0
          const record = records[node]
          if (keep ? !eligibleNodes[node] : record.payload === undefined || needed[node]) continue
          const proposedScore = score + Number(keep)
          if (proposedScore + maximum[node + 1] < goal || proposedScore + minimum[node + 1] > goal)
            continue
          if (keep) {
            const storage = storages[node]
            if (shared && owners.has(storage)) continue
            let compatible = true
            const edges = record.edges
            for (let position = 0; position < edges.length; position += 1) {
              const edge = edges[position]
              if (!isNode(edge)) continue
              const child = edge.node
              if (!Number.isInteger(child) || child < 0 || child >= size)
                throw finalizationChildInvalid(node, child)
              if (child < node && !retained[child]) {
                compatible = false
                break
              }
            }
            if (!compatible) continue
            checkpoints[node] = trail.length
            for (const edge of record.edges) {
              if (!isNode(edge) || edge.node <= node || needed[edge.node]) continue
              needed[edge.node] = true
              trail.push(edge.node)
            }
            if (shared) owners.add(storage)
          }
          retained[node] = keep
          score = proposedScore
          node += 1
          if (node < size) next[node] = 0
          continue
        }
      }
      node -= 1
      if (node >= 0 && retained[node]) {
        while (trail.length > checkpoints[node]) needed[trail.pop()!] = false
        if (shared) owners.delete(storages[node])
        score -= 1
      }
    }
  }
}
