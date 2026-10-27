import { isNode } from './edge'
import type { ImmutableProblem } from '../types'
import { denseArray } from '../standard-prototypes'

/**
 * Returns the mask keeping exactly the eligible records when every fixed record is eligible, and
 * undefined otherwise. Each record is its own storage, so no two kept records share one, and the
 * unavailable records are closed over parents, so every child of an eligible record is eligible:
 * the mask is then the first that `immutableSelections` streams (CompactImmutable.ranked_head).
 */
export function immutableHead({ records, unavailable }: ImmutableProblem): boolean[] | undefined {
  const size = records.length
  const keep = denseArray<boolean>(size)
  for (let node = 0; node < size; node += 1) {
    keep[node] = !unavailable.has(node)
    if (!keep[node] && records[node].payload === undefined) return undefined
  }
  return keep
}

/**
 * Streams immutable retained-node masks in descending score and keep-before-fresh order.
 *
 * @remarks
 * The stream must be `CompactImmutable.ranked`, whose masks decode to the reference ranked plans
 * (CompactImmutable.ranked_decode), and the score bounds keep every completion at the current
 * score (GraphPolicy.completion_survives_score_pruning). No theorem covers this search, the edge
 * test and the `needed` trail included; the CompactImmutable bridge compares its stream with
 * `ranked`. Each record is its own storage, so no kept records share one
 * (CompactImmutable.separated_of_injective) and the search tracks no owners. Every retained edge
 * demands the child's sole proposed identity, so forward demands are Boolean. Only newly installed
 * demands enter the trail; undo preserves older demands.
 */
// fallow-ignore-next-line complexity -- per-step helper calls in this search slowed produce 1%
export function* immutableSelections({
  records,
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
  for (let node = size - 1; node >= 0; node -= 1) {
    retained[node] = false
    needed[node] = false
    const eligible = !unavailable.has(node)
    eligibleNodes[node] = eligible
    const fixed = records[node].payload === undefined
    if (fixed && !eligible) return
    maximum[node] = maximum[node + 1] + Number(eligible)
    minimum[node] = minimum[node + 1] + Number(fixed)
  }
  const next = denseArray<number>(size)
  const checkpoints = denseArray<number>(size)
  const trail: number[] = []
  for (let goal = maximum[0]; goal >= minimum[0]; goal -= 1) {
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
            let compatible = true
            const edges = record.edges
            for (let position = 0; position < edges.length; position += 1) {
              const edge = edges[position]
              if (!isNode(edge)) continue
              const child = edge.node
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
        score -= 1
      }
    }
  }
}
