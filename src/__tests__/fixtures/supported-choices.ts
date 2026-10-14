import type { Domains } from '../../types'

/** Small domains with repeated labels, missing targets, and disjunctive support. */
export function supportedChoiceDomains(variant: number): Domains {
  let seed = variant + 9137
  const random = (limit: number): number => {
    seed = (Math.imul(seed, 1_664_525) + 1_013_904_223) >>> 0
    return (seed >>> 8) % limit
  }
  return Array.from({ length: 3 }, (_, node) =>
    Array.from({ length: 3 }, (_, index) => ({
      identity: node * 2 + (index % 2),
      required: Array.from({ length: random(3) }, () => ({
        identity: random(7),
        node: random(4),
      })),
      retained: index !== 2,
      storage: random(7),
    })),
  )
}
