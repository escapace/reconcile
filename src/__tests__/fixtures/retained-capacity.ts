import type { Domains } from '../../types'

// The first owner collision arrives while root's cyclic follower is still unselected.
// Both root and node 1 have duplicated active demands on that future follower.
export function retainedCapacityDomains(): Domains {
  return [
    [
      {
        identity: 0,
        required: [
          { identity: 4, node: 4 },
          { identity: 4, node: 4 },
        ],
        retained: true,
        storage: 0,
      },
    ],
    [
      {
        identity: 1,
        required: [
          { identity: 4, node: 4 },
          { identity: 4, node: 4 },
        ],
        retained: true,
        storage: 1,
      },
      { identity: 11, required: [], retained: false, storage: 101 },
    ],
    [
      { identity: 2, required: [], retained: true, storage: 20 },
      { identity: 12, required: [], retained: false, storage: 102 },
    ],
    [
      { identity: 3, required: [], retained: true, storage: 20 },
      { identity: 13, required: [], retained: false, storage: 103 },
    ],
    [
      { identity: 4, required: [{ identity: 0, node: 0 }], retained: true, storage: 4 },
      { identity: 14, required: [], retained: false, storage: 104 },
    ],
  ]
}
