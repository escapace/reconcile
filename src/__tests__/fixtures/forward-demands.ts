import type { Domains } from '../../types'

export function forwardDemandDomains(variant: number): Domains {
  const demand = { identity: (variant & 1) === 0 ? 8 : 7, node: 3 }
  return [
    [{ identity: 0, required: [{ identity: 7, node: 3 }], retained: true, storage: 0 }],
    [
      {
        identity: 1,
        required: [
          demand,
          ...((variant & 4) === 0 ? [] : [{ ...demand }]),
          ...((variant & 8) === 0 ? [] : [{ identity: 7, node: 3 }]),
        ],
        retained: true,
        storage: 1,
      },
      { identity: 10, required: [], retained: false, storage: 1 },
    ],
    [
      { identity: 20, required: [{ identity: 20, node: 2 }], retained: true, storage: 2 },
      { identity: 21, required: [], retained: true, storage: 2 },
    ],
    [7, 8].map((identity) => ({
      identity,
      required: (variant & 2) === 0 ? [] : [{ identity: 0, node: 0 }],
      retained: true,
      storage: 3,
    })),
  ]
}
