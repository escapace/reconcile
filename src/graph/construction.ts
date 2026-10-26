/**
 * Orders fresh allocations over sealed construction dependencies: the fresh nodes without any,
 * then the fresh nodes with some, each group ascending. Retained identities are already
 * available. Empty-dependency shells come first, preserving the built-in shell-before-view
 * observation boundary.
 *
 * @remarks
 * A dependency names a buffer or a URL's `searchParams`, whose kind has none of its own, so each
 * dependency of a fresh node is retained or allocated in the first group. This order,
 * `Construction.flatSchedule`, is then the wave schedule of `Graph.Construction`
 * (Construction.schedule_flat), which the CompactImmutable bridge checks. The caller must finish
 * this schedule before performing any native allocation.
 *
 * @returns The complete allocation order.
 */
export function constructionOrder(
  dependencies: ReadonlyArray<readonly number[]>,
  retained: readonly boolean[],
): number[] {
  const order: number[] = []
  const dependents: number[] = []
  for (let node = 0; node < dependencies.length; node += 1)
    if (!retained[node]) (dependencies[node].length === 0 ? order : dependents).push(node)
  for (let index = 0; index < dependents.length; index += 1) order.push(dependents[index])
  return order
}
