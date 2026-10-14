import { assert, it } from 'vitest'
import { reactive } from 'vue'

import { produce } from '../index'
import { greatestRetainedSubset, hasEdge } from './fixtures/public-api-fuzz'

interface Node {
  value: number
  e0?: Node
  e1?: Node
  e2?: Node
}

it.each([false, true])('preserves many parallel edges and distinct storage (undo: %s)', (undo) => {
  const child = { value: 0 }
  const current = {
    aliases: Array.from({ length: 140_000 }, () => child),
    wrapped: reactive(child),
  }
  const next = produce(current, (draft) => {
    draft.aliases[0].value = 1
    if (undo) draft.aliases[0].value = 0
    return draft
  })

  assert.notEqual(next, current)
  if (undo) {
    // Keeping the array and raw child preserves two identities. Pinning the
    // untouched wrapper would preserve only one and discard both compatible nodes.
    assert.equal(next.aliases, current.aliases)
    assert.equal(next.aliases[0], child)
    assert.notEqual(next.wrapped, current.wrapped)
  } else {
    assert.notEqual(next.aliases, current.aliases)
    assert.notEqual(next.aliases[0], child)
    assert.equal(next.wrapped, current.wrapped)
  }
  assert.equal(next.aliases.length, current.aliases.length)
  for (const alias of next.aliases) assert.equal(alias, next.aliases[0])
  for (const alias of current.aliases) assert.equal(alias, child)
  assert.equal(next.aliases[0].value, undo ? 0 : 1)
  const replacement = undo ? next.wrapped : next.aliases[0]
  replacement.value = 7
  assert.equal(child.value, 0)
  assert.equal(undo ? next.aliases[0].value : next.wrapped.value, 0)
})

it('chooses the larger compatible subset independently of undo bookkeeping', () => {
  for (const reverse of [false, true]) {
    for (let touched = 0; touched < 16; touched += 1) {
      const raw = { value: 0 }
      const parent = { child: raw, value: 0 }
      const wrapped = reactive(raw)
      const current = reverse
        ? { ...{ right: wrapped }, left: parent, value: 0 }
        : { left: parent, right: wrapped, value: 0 }
      const next = produce(current, (draft) => {
        for (let id = 0; id < 4; id += 1) {
          if ((touched & (1 << id)) === 0) continue
          const node =
            id === 0 ? draft : id === 1 ? draft.left : id === 2 ? draft.left.child : draft.right
          node.value = 1
          node.value = 0
        }
        return draft
      })
      assert.notEqual(next, current)
      assert.equal(next.left, parent)
      assert.equal(next.left.child, raw)
      assert.notEqual(next.right, wrapped)
      next.right.value = 9
      assert.equal(raw.value, 0)
      assert.equal(wrapped.value, 0)
    }
  }
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
  'retains the larger untouched %s subtree while separating conflicting storage',
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
    const current = { flag: 0, left: untouched, repeated: untouched, right: reactive(raw), sibling }
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
    assert.notEqual(next.right, current.right)
    next.right.n = 9
    assert.equal(raw.n, 0)
    assert.equal(current.right.n, 0)
  },
)

it.each([false, true])('separates two untouched subtrees (unrelated undo: %s)', (undo) => {
  const raw = { n: 0 }
  const left = { child: raw, self: undefined as unknown }
  left.self = left
  const sibling = { n: 0 }
  const current = { flag: 0, left, repeated: left, right: reactive(raw), sibling }
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
  next.right.n = 9
  assert.equal(next.left.child.n, 0)
})

it.each(['draft', 'replacement'] as const)('checks untouched storage for a %s return', (mode) => {
  const raw = { n: 0 }
  const current = { left: raw, right: reactive(raw) }
  const next = produce(current, (draft) => (mode === 'draft' ? draft : { ...current }))
  assert.equal(raw.n, 0)
  next.right.n = 9
  assert.equal(next.left.n, 0)
})

it('preserves explicit cancellation despite overlapping storage', () => {
  const raw = { n: 0 }
  const current = { left: raw, right: reactive(raw) }
  const next = produce(current, (draft) => {
    draft.left.n = 1
    return current
  })
  assert.equal(next, current)
  assert.equal(raw.n, 0)
})

it('selects the greater immutable reuse count across a storage conflict and parent dependency', () => {
  const raw = { value: 0 }
  const wrapped = reactive(raw)
  const current = { first: raw, second: { child: wrapped } }
  const result = produce(current, (draft) => {
    draft.first.value = 1
    draft.first.value = 0
    draft.second.child.value = 1
    draft.second.child.value = 0
    return draft
  })
  assert.notEqual(result, current)
  assert.notEqual(result.first, raw)
  assert.equal(result.second, current.second)
  assert.equal(result.second.child, wrapped)
  assert.equal(result.first.value, 0)
  assert.equal(raw.value, 0)
})
