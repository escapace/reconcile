import { assert, describe, it } from 'vitest'

import { produce } from '../produce'
import { reconcile } from '../reconcile'

/**
 * Focused regression coverage for the monotonic write migration.
 *
 * These tests lock down areas that are easy to regress while refactoring:
 * - returning an unmodified nested draft handle must unwrap back to the base value
 * - recipe-result and caller-publication identities after revert-style writes
 * - `Set` delete-plus-add preserves ordinary membership and order semantics
 */
describe('caller publication monotonic write regressions', () => {
  it('returns the original nested map when an unmodified map draft handle is returned', () => {
    const current = {
      map: new Map<string, number>([['key', 1]]),
    }

    const result = produce(current, (draft) => {
      assert.equal(draft.map.get('key'), 1)
      return draft.map
    })

    // Returning an unmodified nested draft handle must unwrap back to the base collection rather
    // than leaking the internal draft wrapper to the caller.
    assert.equal(result, current.map)
    assert.equal(result instanceof Map, true)
    assert.deepEqual(Array.from(result.entries()), [['key', 1]])
  })

  it('returns the original nested set when an unmodified set draft handle is returned', () => {
    const current = {
      set: new Set<number>([1, 2, 3]),
    }

    const result = produce(current, (draft) => {
      assert.equal(draft.set.has(2), true)
      return draft.set
    })

    // Returning an unmodified nested draft handle must unwrap back to the base collection rather
    // than leaking the internal draft wrapper to the caller.
    assert.equal(result, current.set)
    assert.equal(result instanceof Set, true)
    assert.deepEqual(Array.from(result.values()), [1, 2, 3])
  })

  it('restores both produce and caller publication identity after mutate-then-revert on the same nested property', () => {
    const current = {
      nested: { count: 0 },
    }

    const next = produce(current, (draft) => {
      draft.nested.count = 1
      draft.nested.count = 0
      return draft
    })

    const published = reconcile(
      current,
      produce(current, (draft) => {
        draft.nested.count = 1
        draft.nested.count = 0
        return draft
      }),
    )

    assert.equal(next, current)
    assert.equal(next.nested, current.nested)
    assert.deepEqual(next, { nested: { count: 0 } })

    assert.equal(published, current)
    assert.equal(published.nested, current.nested)
    assert.deepEqual(published, { nested: { count: 0 } })
  })

  it('treats set delete plus add of the same value as a sticky mutation', () => {
    const current = {
      set: new Set([1, 2, 3]),
    }

    const result = produce(current, (draft) => {
      draft.set.delete(1)
      draft.set.add(1)
      return draft.set
    })

    // There is no restoration for sets. Delete-plus-add is ordinary mutation, so the returned set
    // is a fresh finalized image even though the final membership matches the original set.
    assert.notEqual(result, current.set)
    assert.deepEqual(Array.from(result.values()), [2, 3, 1])
    assert.deepEqual(Array.from(current.set.values()), [1, 2, 3])
  })
})
