import { isNode } from './edge'
import { finalizationChildInvalid, finalizationStorageMissing } from '../error'
import type { ImmutableProblem } from '../types'

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
  const maximum = new Array<number>(size + 1).fill(0)
  const minimum = new Array<number>(size + 1).fill(0)
  const owners = new Set<object>()
  for (let node = size - 1; node >= 0; node -= 1) {
    const eligible = !unavailable.has(node)
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
  owners.clear()
  const retained = new Array<boolean>(size).fill(false)
  const needed = new Array<boolean>(size).fill(false)
  const next = new Uint8Array(size)
  const checkpoints = new Array<number>(size)
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
          if (keep ? unavailable.has(node) : record.payload === undefined || needed[node]) continue
          const proposedScore = score + Number(keep)
          if (proposedScore + maximum[node + 1] < goal || proposedScore + minimum[node + 1] > goal)
            continue
          if (keep) {
            const storage = storages[node]
            if (owners.has(storage)) continue
            let compatible = true
            for (const edge of record.edges) {
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
            owners.add(storage)
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
        owners.delete(storages[node])
        score -= 1
      }
    }
  }
}
