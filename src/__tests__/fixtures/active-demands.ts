import type { Domains } from '../../types'

/** Finite witnesses for duplicate updates, conflicts, backward edges and tier restoration. */
export function activeDemandDomains(variant: number): Domains {
  return Array.from({ length: 4 }, (_, node) =>
    Array.from({ length: 2 }, (_, option) => {
      const identity = node * 10 + option
      const required = [{ identity, node }]
      if (node < 2 && (option === 0 || (variant & 1) !== 0)) {
        const demand = { identity: 30 + ((variant >> (node + 1)) & 1), node: 3 }
        required.push(demand, { ...demand })
      }
      if (node === 2 && (variant & 8) !== 0)
        required.push({ identity: (variant >> 4) & 1, node: 0 })
      if (node === 3 && (variant & 32) !== 0)
        required.push({ identity: 10 + ((variant >> 6) & 1), node: 1 })
      return { identity, required, retained: option === 0, storage: identity }
    }),
  )
}
