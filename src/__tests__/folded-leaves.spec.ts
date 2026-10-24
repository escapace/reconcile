import { assert, it } from 'vitest'
import { produce } from '../index'

it('keeps an unchanged subtree whose object a change also references', () => {
  const inner = { n: 0 }
  const current = { changed: { n: 0, ref: undefined as unknown }, kept: { deep: { inner } } }
  const result = produce(current, (draft) => {
    draft.changed.n = 1
    draft.changed.ref = draft.kept.deep.inner
    return draft
  })
  assert.strictEqual(result.kept, current.kept)
  assert.strictEqual(result.changed.ref, inner)
})

it('keeps an unchanged subtree whose object the recipe moves elsewhere as itself', () => {
  const moved = { n: 0 }
  const current = { changed: { copy: undefined as unknown, n: 0 }, kept: { deep: { moved } } }
  const result = produce(current, (draft) => {
    draft.changed.n = 1
    // The original, not its draft: a record of an unchanged object inside a kept subtree.
    draft.changed.copy = current.kept.deep.moved
    return draft
  })
  assert.strictEqual(result.kept, current.kept)
  assert.strictEqual(result.changed.copy, moved)
})
