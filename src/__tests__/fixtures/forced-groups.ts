import type { Choice, Domains } from '../../types'

/** Finite rings and dense alternatives exercise SCCs, conflicts and duplicate supports. */
export function forcedGroupDomains(variant: number): Domains {
  const size = 2 + (variant % 4)
  const domains: Choice[][] = Array.from({ length: size }, (_, node) => [
    {
      identity: node * 2,
      required: [{ identity: ((node + 1) % size) * 2, node: (node + 1) % size }],
      retained: (variant & 4) === 0 || node % 2 === 0,
      storage: (variant & 8) === 0 ? node * 2 : node % 2,
    },
    {
      identity: node * 2 + ((variant & 16) === 0 || node !== 1 ? 1 : 0),
      required:
        (variant & 32) === 0
          ? []
          : [{ identity: ((node + size - 1) % size) * 2 + 1, node: (node + size - 1) % size }],
      retained: false,
      storage: node * 2 + 1,
    },
  ])
  if ((variant & 64) !== 0)
    domains[0][0] = {
      ...domains[0][0],
      required: [...domains[0][0].required, { identity: size * 2, node: size }],
    }
  if ((variant & 128) !== 0)
    domains[0][1] = { ...domains[0][1], required: [{ identity: 2, node: 1 }] }
  return domains
}
