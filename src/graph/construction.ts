import { denseArray } from '../standard-prototypes'
/**
 * Orders fresh allocations in stable waves over sealed construction dependencies.
 * Retained identities are already available. Empty-dependency shells form the
 * first wave, preserving the built-in shell-before-view observation boundary.
 *
 * @remarks
 * The scheduler counts reverse dependency occurrences, including duplicates, then emits stable level
 * buckets. Queue order alone is not the required allocation order; the result equals the wave
 * schedule of `Graph.Construction`, which the CompactImmutable bridge checks.
 * Node IDs must form a closed dense domain. Counters are plain numbers, exact far beyond any
 * occurrence count, as the model's naturals are.
 * The caller must finish this schedule before performing any native allocation.
 *
 * @returns The complete allocation order, or undefined when no safe fresh order exists.
 */
// Fresh nodes without construction inputs are all shells at level 0, so when every fresh
// node is one the order is the fresh nodes ascending (Construction.schedule_shells_only).
function freshShells(
  dependencies: ReadonlyArray<readonly number[]>,
  retained: readonly boolean[],
): number[] | undefined {
  const shells: number[] = []
  for (let node = 0; node < dependencies.length; node += 1)
    if (!retained[node]) {
      if (dependencies[node].length !== 0) return undefined
      shells.push(node)
    }
  return shells
}

export function constructionOrder(
  dependencies: ReadonlyArray<readonly number[]>,
  retained: readonly boolean[],
): number[] | undefined {
  const size = dependencies.length
  const shells = freshShells(dependencies, retained)
  if (shells !== undefined) return shells
  // Only fresh nodes are counted and levelled, so only they are initialized. Plain arrays avoid
  // a typed array's separate backing store once it exceeds V8's small on-heap size.
  const remaining = denseArray<number>(size)
  const levels = denseArray<number>(size)
  const parents = denseArray<number[] | undefined>(size)
  const queue: number[] = []
  let fresh = 0
  for (let node = 0; node < size; node += 1) {
    if (retained[node]) continue
    fresh += 1
    const prerequisites = dependencies[node]
    remaining[node] = 0
    levels[node] = Number(prerequisites.length !== 0)
    for (const dependency of prerequisites) {
      if (retained[dependency]) continue
      remaining[node] += 1
      ;(parents[dependency] ??= []).push(node)
    }
    if (remaining[node] === 0) queue.push(node)
  }
  // Releases dependents in queue order and raises each one above its deepest fresh prerequisite.
  const release = (): void => {
    for (let cursor = 0; cursor < queue.length; cursor += 1) {
      const dependency = queue[cursor]
      const nextLevel = levels[dependency] + 1
      const dependents = parents[dependency]
      if (dependents === undefined) continue
      for (const parent of dependents) {
        levels[parent] = Math.max(levels[parent], nextLevel)
        remaining[parent] -= 1
        if (remaining[parent] === 0) queue.push(parent)
      }
    }
  }
  release()
  if (queue.length !== fresh) return undefined
  const buckets = denseArray<number[] | undefined>(size + 1)
  for (let node = 0; node < size; node += 1)
    if (!retained[node]) (buckets[levels[node]] ??= []).push(node)
  // Concatenates the levels in order; a level that no node reached is a hole.
  const flatten = (): number[] => {
    const order: number[] = []
    for (const level of buckets) if (level !== undefined) for (const node of level) order.push(node)
    return order
  }
  return flatten()
}
