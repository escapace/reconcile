import assert from 'node:assert/strict'
import { it } from 'vitest'

import { produce } from '../index'

it('keeps cached array children coherent across moves, holes, and length changes', () => {
  const first = { value: 1 }
  const second = { value: 2 }
  const items = new Array<typeof first | undefined>(4)
  items[0] = first
  items[2] = second
  items[3] = first
  const current = { first, items, second }
  const before = structuredClone(current)
  const expected = structuredClone(current)

  const recipe = (draft: typeof current) => {
    const held = draft.items[0]!
    assert.equal(draft.items[2], draft.second)
    draft.items.copyWithin(1, 0, 3)
    draft.items.splice(0, 1, draft.second)
    draft.items.length = 6
    draft.items.reverse()
    draft.items[2].value = 7
    held.value = 9
    return draft
  }

  recipe(expected)
  const result = produce(current, recipe)
  assert.deepStrictEqual(current, before)
  assert.deepStrictEqual(result, expected)
  assert.equal(result.items[4], result.first)
  assert.equal(result.items[2], result.second)
  assert.equal(result.items[5], result.second)
})
