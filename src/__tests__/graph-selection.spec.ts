import { assert, it } from 'vitest'
import { forcedGroupDomains } from './fixtures/forced-groups'
import { activeDemandDomains } from './fixtures/active-demands'
import { forwardDemandDomains } from './fixtures/forward-demands'
import { retainedCapacityDomains } from './fixtures/retained-capacity'
import { headSelection, selections } from '../graph/selection'
import type { Choice, Domains } from '../types'

// Deliberately enumerate all tuples before checking whole-plan constraints.
// This oracle does not share the production search or partial pruning logic.
function oracle(domains: Domains): number[][] {
  let plans: number[][] = [[]]
  for (const domain of domains)
    plans = plans.flatMap((plan) => domain.map((_, index) => [...plan, index]))
  const score = (plan: number[]): number =>
    plan.reduce((count, choice, node) => count + Number(domains[node][choice].retained), 0)
  return plans
    .filter((plan) => {
      const choices = plan.map((choice, node) => domains[node][choice])
      return (
        new Set(choices.map((choice) => choice.storage)).size === choices.length &&
        choices.every((choice) =>
          choice.required.every((edge) => choices[edge.node]?.identity === edge.identity),
        )
      )
    })
    .sort((left, right) => score(right) - score(left))
}

it('streams exactly the feasible plans in retention and traversal order', () => {
  let seed = 17_219
  const random = (size: number): number => {
    seed = (Math.imul(seed, 1_664_525) + 1_013_904_223) >>> 0
    return (seed >>> 8) % size
  }
  for (let test = 0; test < 1200; test += 1) {
    const size = random(5)
    const domains: Choice[][] = Array.from({ length: size }, (_, node) =>
      Array.from({ length: random(4) }, (_, option) => ({
        identity: option * 5 + node,
        required: Array.from({ length: random(3) }, () => ({
          identity: random(16),
          node: random(size + 1),
        })),
        retained: random(2) === 1,
        storage: random(5),
      })),
    )
    const before = JSON.stringify(domains)
    assert.deepEqual([...selections(domains)], oracle(domains), `fixture ${test}`)
    assert.equal(JSON.stringify(domains), before)
  }
})

// GraphPolicy.rankedPreferred_head: a feasible, maximal head plan is the stream's first plan
// while the top tier has no preference, and a stream resumed after it repeats nothing.
it('takes the head plan first and resumes the stream after it', () => {
  let seed = 40_123
  const random = (size: number): number => {
    seed = (Math.imul(seed, 1_664_525) + 1_013_904_223) >>> 0
    return (seed >>> 8) % size
  }
  let heads = 0
  let declined = 0
  for (let test = 0; test < 3000; test += 1) {
    const size = 1 + random(5)
    const domains: Choice[][] = Array.from({ length: size }, (_, node) =>
      Array.from({ length: 1 + random(3) }, (_, option) => ({
        identity: option * 5 + node,
        required: Array.from({ length: random(4) === 0 ? 1 + random(2) : 0 }, () => {
          const target = random(size + 1)
          return { identity: random(3) === 0 ? random(16) : 5 * random(2) + target, node: target }
        }),
        retained: random(3) !== 0,
        storage: random(3) === 0 ? random(4) : 10 + option * 5 + node,
      })),
    )
    const head = headSelection(domains)
    const tiers = new Map<number, Set<number>>()
    const top = head?.reduce(
      (count, choice, node) => count + Number(domains[node][choice].retained),
      0,
    )
    // Preferences differ per tier and stay fixed for the stream; the head's tier has none.
    const preferFresh = (score: number): ReadonlySet<number> => {
      if (score === top) return new Set()
      let preferred = tiers.get(score)
      if (preferred === undefined) {
        preferred = new Set(Array.from({ length: random(size + 1) }, () => random(size)))
        tiers.set(score, preferred)
      }
      return preferred
    }
    const stream = [...selections(domains, preferFresh)]
    if (head === undefined) {
      declined += 1
      continue
    }
    heads += 1
    assert.deepEqual(stream[0], head, `fixture ${test}`)
    // The head attempt may record failures before the search starts; the top tier keeps the
    // order it would have had, since its preference was due before any attempt.
    const afterHead = (score: number): ReadonlySet<number> =>
      score === top ? new Set(domains.keys()) : preferFresh(score)
    // As the driver does: the first preference asked for is the top tier's, answered with none.
    let ordinary = true
    const resumed = (score: number): ReadonlySet<number> => {
      if (!ordinary) return afterHead(score)
      ordinary = false
      return new Set()
    }
    assert.deepEqual([...selections(domains, resumed)].slice(1), stream.slice(1), `fixture ${test}`)
  }
  assert.isAbove(heads, 300)
  assert.isAbove(declined, 300)
})

it('handles shared views and immutable cyclic reuse through the same dependency constraints', () => {
  const domains: Domains = [
    [
      { identity: 0, required: [], retained: true, storage: 0 },
      { identity: 1, required: [], retained: true, storage: 1 },
      { identity: 2, required: [], retained: false, storage: 2 },
    ],
    [
      { identity: 3, required: [{ identity: 1, node: 0 }], retained: true, storage: 3 },
      { identity: 4, required: [], retained: false, storage: 4 },
    ],
    [
      { identity: 5, required: [{ identity: 1, node: 0 }], retained: true, storage: 5 },
      { identity: 6, required: [], retained: false, storage: 6 },
    ],
  ]
  assert.deepEqual(selections(domains).next().value, [1, 0, 0])
  const cycle: Domains = [
    [
      { identity: 0, required: [{ identity: 1, node: 1 }], retained: true, storage: 0 },
      { identity: 2, required: [], retained: false, storage: 2 },
    ],
    [
      { identity: 1, required: [{ identity: 0, node: 0 }], retained: true, storage: 1 },
      { identity: 3, required: [], retained: false, storage: 3 },
    ],
  ]
  assert.deepEqual(
    [...selections(cycle)],
    [
      [0, 0],
      [1, 1],
    ],
  )
})

it('does not retain storage owned by a fixed root or a distinct equal-valued wrapper', () => {
  const domains: Domains = [
    [{ identity: 0, required: [], retained: true, storage: 0 }],
    [
      { identity: 1, required: [], retained: true, storage: 0 },
      { identity: 2, required: [], retained: false, storage: 1 },
    ],
  ]
  assert.deepEqual([...selections(domains)], [[0, 1]])
})

it('preserves future forced followers and duplicate demands across an infeasible retention tier', () => {
  const problem = retainedCapacityDomains()
  const frozen = JSON.stringify(problem)
  const expected = oracle(problem)
  assert.isAbove(expected.length, 0)
  assert.deepEqual(expected[0], [0, 0, 0, 1, 0])
  const tiers: number[] = []
  const actual = [
    ...selections(problem, (rank) => {
      tiers.push(rank)
      return new Set<number>()
    }),
  ]
  assert.deepEqual(actual, expected)
  assert.deepEqual(tiers, [5, 4, 3, 2, 1])
  const stream = selections(problem)
  assert.deepEqual(stream.next().value, expected[0])
  stream.return()
  assert.deepEqual([...selections(problem)], expected)
  assert.equal(JSON.stringify(problem), frozen)
})

it.each([1, 2, 4, 8, 16, 32, 64])(
  'preserves the complete stream for forward requirement domains of width %s',
  (width) => {
    const domains: Domains = [
      Array.from({ length: width }, (_, identity) => ({
        identity,
        required: [{ identity: width + identity, node: 1 }],
        retained: true,
        storage: identity,
      })),
      Array.from({ length: width }, (_, option) => ({
        identity: width + option,
        required: [],
        retained: true,
        storage: width + option,
      })),
    ]
    assert.deepEqual([...selections(domains)], oracle(domains))
  },
)

it('uses a bounded stack and returns independent plans', () => {
  const domains: Domains = Array.from({ length: 2000 }, (_, identity) => [
    { identity, required: [], retained: true, storage: identity },
  ])
  const search = selections(domains)
  assert.deepEqual(search.next().value, new Array(2000).fill(0))
  assert.isTrue(search.next().done)
  const small: Domains = [
    [
      { identity: 0, required: [], retained: true, storage: 0 },
      { identity: 1, required: [], retained: false, storage: 1 },
    ],
  ]
  const plans = selections(small)
  const first = plans.next().value
  assert.deepEqual(plans.next().value, [1])
  assert.deepEqual(first, [0])
})

it('changes only tie order when failure preferences differ between score tiers', () => {
  for (let fixture = 0; fixture < 200; fixture += 1) {
    const domains: Domains = Array.from({ length: 4 }, (_, node) => [
      { identity: node * 3, required: [], retained: true, storage: (fixture + node) % 3 },
      { identity: node * 3 + 1, required: [], retained: true, storage: (fixture * 3 + node) % 5 },
      { identity: node * 3 + 2, required: [], retained: false, storage: node + 10 },
    ])
    const preferences = (rank: number): ReadonlySet<number> =>
      new Set([0, 1, 2, 3].filter((node) => (fixture + rank + node) % 3 === 0))
    const score = (plan: readonly number[]): number =>
      plan.reduce((sum, choice, node) => sum + Number(domains[node][choice].retained), 0)
    const expected = oracle(domains).sort((a, b) => {
      const rank = score(a)
      if (rank !== score(b)) return score(b) - rank
      for (let node = 0; node < domains.length; node += 1) {
        if (a[node] === b[node]) continue
        const retention = preferences(rank).has(node)
          ? Number(domains[node][a[node]].retained) - Number(domains[node][b[node]].retained)
          : 0
        return retention !== 0 ? retention : a[node] - b[node]
      }
      return 0
    })
    assert.deepEqual([...selections(domains, preferences)], expected)
  }
})

it('restores duplicate and conflicting active demands across backtracking and score tiers', () => {
  for (let variant = 0; variant < 128; variant += 1) {
    const domains = activeDemandDomains(variant)
    const expected = oracle(domains)
    assert.deepEqual([...selections(domains)], expected, `variant ${variant}`)
    const suspended = selections(domains)
    const first = suspended.next()
    assert.deepEqual(first.value, expected[0])
    suspended.return()
    assert.deepEqual([...selections(domains)], expected)
  }
})

it('preserves complete streams and every preference callback when pruning future clashes', () => {
  for (let variant = 0; variant < 16; variant += 1) {
    const domains = forwardDemandDomains(variant)
    const expected = oracle(domains)
    assert.isAbove(expected.length, 0)
    assert.deepEqual([...selections(domains)], expected)
    const tiers: number[] = []
    const actual = [
      ...selections(domains, (rank) => {
        tiers.push(rank)
        return new Set(rank === 4 ? [1] : [])
      }),
    ]
    // Node 1's fresh choice cannot occur at score 4, so this preference keeps ties.
    assert.deepEqual(actual, expected)
    assert.deepEqual(tiers, [4, 3])
    const suspended = selections(domains)
    assert.deepEqual(suspended.next().value, expected[0])
    suspended.return()
    assert.deepEqual([...selections(domains)], expected)
  }
})

it('preserves every cyclic group plan, including duplicate supports and conflicting groups', () => {
  for (let variant = 0; variant < 256; variant += 1) {
    const domains = forcedGroupDomains(variant)
    const expected = oracle(domains)
    assert.deepEqual([...selections(domains)], expected, `group ${variant}`)
    const score = (plan: readonly number[]): number =>
      plan.reduce((sum, choice, node) => sum + Number(domains[node][choice].retained), 0)
    const preferences = (rank: number): ReadonlySet<number> =>
      new Set(domains.map((_, node) => node).filter((node) => (variant + node + rank) % 2 === 0))
    const preferred = expected.slice().sort((a, b) => {
      const rank = score(a)
      if (rank !== score(b)) return score(b) - rank
      for (let node = 0; node < domains.length; node += 1) {
        if (a[node] === b[node]) continue
        const retention = preferences(rank).has(node)
          ? Number(domains[node][a[node]].retained) - Number(domains[node][b[node]].retained)
          : 0
        return retention !== 0 ? retention : a[node] - b[node]
      }
      return 0
    })
    assert.deepEqual([...selections(domains, preferences)], preferred, `preferred group ${variant}`)
    const suspended = selections(domains)
    assert.deepEqual(suspended.next().value, expected[0])
    suspended.return()
    assert.deepEqual([...selections(domains)], expected)
  }
})

it('restores competing future group owners after the earlier group is undone', () => {
  const domains: Domains = [
    [
      { identity: 0, required: [{ identity: 4, node: 2 }], retained: true, storage: 0 },
      { identity: 1, required: [], retained: false, storage: 1 },
    ],
    [
      { identity: 2, required: [{ identity: 5, node: 2 }], retained: true, storage: 2 },
      { identity: 3, required: [], retained: false, storage: 3 },
    ],
    [
      { identity: 4, required: [{ identity: 0, node: 0 }], retained: true, storage: 4 },
      { identity: 5, required: [{ identity: 2, node: 1 }], retained: true, storage: 5 },
      { identity: 6, required: [], retained: false, storage: 6 },
    ],
  ]
  assert.deepEqual([...selections(domains)], oracle(domains))
})

it('rejects a component containing different choices for the same owner', () => {
  const domains: Domains = [
    [
      { identity: 0, required: [{ identity: 2, node: 1 }], retained: true, storage: 0 },
      { identity: 1, required: [{ identity: 0, node: 0 }], retained: false, storage: 1 },
    ],
    [{ identity: 2, required: [{ identity: 1, node: 0 }], retained: true, storage: 2 }],
  ]
  assert.deepEqual([...selections(domains)], oracle(domains))
  assert.deepEqual([...selections(domains)], [])
})

it('traverses a large mandatory cycle without recursive graph or search stacks', () => {
  const size = 12_000
  const domains: Domains = Array.from({ length: size }, (_, node) => [
    {
      identity: node,
      required: [{ identity: (node + 1) % size, node: (node + 1) % size }],
      retained: true,
      storage: node,
    },
  ])
  assert.deepEqual([...selections(domains)], [new Array(size).fill(0)])
})
