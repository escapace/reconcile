import { assert, it } from 'vitest'

import { produce } from '../index'
import { greatestRetainedSubset, hasEdge } from './fixtures/public-api-fuzz'

interface Node {
  value: number
  e0?: Node
  e1?: Node
  e2?: Node
}

// One object at many positions is kept at every position, or replaced at all of them with one
// new object.
it.each([false, true])('keeps many parallel edges as one object (undo: %s)', (undo) => {
  const child = { value: 0 }
  const current = {
    aliases: Array.from({ length: 140_000 }, () => child),
  }
  const next = produce(current, (draft) => {
    draft.aliases[0].value = 1
    if (undo) draft.aliases[0].value = 0
    return draft
  })

  if (undo) assert.equal(next, current)
  else {
    assert.notEqual(next.aliases, current.aliases)
    assert.notEqual(next.aliases[0], child)
  }
  assert.equal(next.aliases.length, current.aliases.length)
  for (const alias of next.aliases) assert.equal(alias, next.aliases[0])
  for (const alias of current.aliases) assert.equal(alias, child)
  assert.equal(next.aliases[0].value, undo ? 0 : 1)
  assert.equal(child.value, 0)
})

it('retains the greatest compatible subset across all three-node graphs and edit masks', () => {
  for (let graph = 0; graph < 512; graph += 1) {
    for (let changed = 0; changed < 8; changed += 1) {
      checkGreatestRetention(graph, changed)
    }
  }
})

const edgeKeys = ['e0', 'e1', 'e2'] as const

function checkGreatestRetention(graph: number, changed: number): void {
  const nodes: Node[] = Array.from({ length: 3 }, () => ({ value: 0 }))
  for (let from = 0; from < 3; from += 1)
    for (let to = 0; to < 3; to += 1)
      if (hasEdge(graph, from, to)) nodes[from][edgeKeys[to]] = nodes[to]

  const greatest = greatestRetainedSubset(graph, changed)

  const current = { nodes }
  const next = produce(current, (draft) => {
    for (let index = 0; index < 3; index += 1) {
      draft.nodes[index].value = 1
      if ((changed & (1 << index)) === 0) draft.nodes[index].value = 0
    }
    return draft
  })
  for (let index = 0; index < 3; index += 1) {
    assertRetainedNode(graph, changed, greatest, nodes, next.nodes, index)
  }
  if (changed === 0) assert.equal(next, current)
}

function assertRetainedNode(
  graph: number,
  changed: number,
  greatest: number,
  nodes: Node[],
  nextNodes: Node[],
  index: number,
): void {
  assert.equal(
    nextNodes[index] === nodes[index],
    Boolean(greatest & (1 << index)),
    `retention graph=${graph} changed=${changed} node=${index}`,
  )
  assert.equal(nodes[index].value, 0)
  assert.equal(nextNodes[index].value, (changed & (1 << index)) !== 0 ? 1 : 0)
  for (let to = 0; to < 3; to += 1)
    if (hasEdge(graph, index, to)) {
      assert.equal(nextNodes[index][edgeKeys[to]], nextNodes[to])
      assert.equal(nodes[index][edgeKeys[to]], nodes[to])
    }
}

it.each(['object', 'array', 'map key', 'map value', 'set'] as const)(
  'keeps an untouched %s subtree holding an object changed back elsewhere',
  (kind) => {
    const raw = { n: 0 }
    const leaf =
      kind === 'array'
        ? [raw]
        : kind === 'map key'
          ? new Map([[raw, 0]])
          : kind === 'map value'
            ? new Map([[0, raw]])
            : kind === 'set'
              ? new Set([raw])
              : { child: raw }
    const untouched = { leaf, self: undefined as unknown }
    untouched.self = untouched
    const sibling = { stable: true }
    const current = { flag: 0, left: untouched, repeated: untouched, right: raw, sibling }
    const next = produce(current, (draft) => {
      draft.flag = 1
      draft.right.n = 1
      draft.right.n = 0
      return draft
    })
    assert.equal(raw.n, 0)
    assert.equal(current.flag, 0)
    assert.equal(next.flag, 1)
    assert.equal(next.left, untouched)
    assert.equal(next.repeated, untouched)
    assert.equal(next.left.self, untouched)
    assert.equal(next.sibling, sibling)
    assert.equal(next.right, current.right)
  },
)

it.each([false, true])(
  'keeps two untouched positions of one object (unrelated undo: %s)',
  (undo) => {
    const raw = { n: 0 }
    const left = { child: raw, self: undefined as unknown }
    left.self = left
    const sibling = { n: 0 }
    const current = { flag: 0, left, repeated: left, right: raw, sibling }
    const next = produce(current, (draft) => {
      draft.flag = 1
      if (undo) {
        draft.sibling.n = 1
        draft.sibling.n = 0
      }
      return draft
    })
    assert.equal(current.flag, 0)
    assert.equal(raw.n, 0)
    assert.equal(next.flag, 1)
    assert.equal(next.left, left)
    assert.equal(next.left, next.repeated)
    assert.equal(next.left.self, next.left)
    assert.equal(next.sibling, sibling)
    assert.equal(next.right, current.right)
  },
)

it.each(['draft', 'replacement'] as const)('keeps both positions for a %s return', (mode) => {
  const raw = { n: 0 }
  const current = { left: raw, right: raw }
  const next = produce(current, (draft) => (mode === 'draft' ? draft : { ...current }))
  if (mode === 'draft') assert.equal(next, current)
  assert.equal(next.left, raw)
  assert.equal(next.right, current.right)
})

it('preserves explicit cancellation of a change through one position', () => {
  const raw = { n: 0 }
  const current = { left: raw, right: raw }
  const next = produce(current, (draft) => {
    draft.left.n = 1
    return current
  })
  assert.equal(next, current)
  assert.equal(raw.n, 0)
})

it('gives every position of a changed object one new object', () => {
  const raw = { value: 0 }
  const current = { first: raw, second: { child: raw }, third: { child: raw } }
  const result = produce(current, (draft) => {
    draft.second.child.value = 1
    return draft
  })
  assert.equal(raw.value, 0)
  assert.notEqual(result.first, raw)
  assert.equal(result.first.value, 1)
  assert.equal(result.second.child, result.first)
  assert.equal(result.third.child, result.first)
  const unchanged = produce(current, (draft) => {
    draft.first.value = 1
    draft.first.value = 0
    draft.second.child.value = 1
    draft.second.child.value = 0
    return draft
  })
  assert.equal(unchanged, current)
})
