import { assert, describe, it } from 'vitest'
import { createPatch, patch } from '../patch'
import { snapshot } from '../snapshot'

/**
 * Verification suite for repeated-reference coherence under the monotonic write model.
 *
 * Core principles:
 * 1. Shared draft-originating values still finalize to one coherent identity.
 * 2. There is no path-level restoration: writing the base reference back does not opt a path
 *    out of shared-image coherence.
 * 3. SameValue writes are true no-ops and do not mark the receiving node modified.
 * 4. Returning the original `current` value from the recipe still bypasses finalization entirely.
 */
describe('Repeated References Semantics (Monotonic Write Model)', () => {
  describe('Plain Objects', () => {
    it('preserves sharing for untouched paths that reach drafted objects (Requirement A wins)', () => {
      const b = { count: 1 }
      const current = { a: { b }, c: { b } }
      const result = createPatch(current, (draft: typeof current) => {
        draft.a.b.count = 2
        // Path 'c' is never accessed. According to the Lean sharedImage theorem,
        // untouched paths reaching a draft-originating object must resolve to
        // the same finalized identity as accessed paths.
        return draft
      })
      // A wins: sharing is preserved for the finalized 'b'
      assert.equal(result.a.b, result.c.b)
      assert.equal(result.a.b.count, 2)
      assert.notEqual(result.a.b, b)
    })

    it('treats writing the base reference back at another path as a SameValue no-op', () => {
      const b = { count: 1 }
      const current = { a: { b }, c: { b } }
      const result = createPatch(current, (draft: typeof current) => {
        draft.a.b.count = 2
        void draft.c
        draft.c.b = current.c.b // SameValue write: no restoration
        return draft
      })
      // Both paths still resolve to one finalized image of `b`.
      assert.equal(result.a.b, result.c.b)
      assert.equal(result.a.b.count, 2)
      assert.notEqual(result.a.b, b)
    })

    it('publishes one coherent shared value through patch()', () => {
      const b = { count: 1 }
      const current = { a: { b }, c: { b } }
      const result = patch(current, (draft: typeof current) => {
        draft.a.b.count = 2
        void draft.c
        draft.c.b = current.c.b // SameValue write: no restoration
        return draft
      })
      assert.equal(result.a.b, result.c.b)
      assert.equal(result.a.b, b)
      assert.equal(b.count, 2)
    })
  })

  describe('Arrays', () => {
    it('preserves sharing for untouched elements of drafted arrays (Requirement A wins)', () => {
      const item = { val: 'a' }
      const current = [item, item]
      const result = createPatch(current, (draft: typeof current) => {
        draft[0].val = 'b'
        // Index 1 is untouched. According to the Lean sharedImage theorem,
        // both indices reach the same draft-originating object, so they
        // must resolve to the same finalized identity.
        return draft
      })
      // A wins: sharing is preserved
      assert.equal(result[0], result[1])
      assert.equal(result[0].val, 'b')
      assert.notEqual(result[0], item)
    })

    it('treats writing the original array element back as a SameValue no-op', () => {
      const item = { val: 'a' }
      const current = [item, item]
      const result = createPatch(current, (draft: typeof current) => {
        draft[0].val = 'b'
        draft[1] = item // SameValue write: no restoration
        return draft
      })
      assert.equal(result[0], result[1])
      assert.equal(result[0].val, 'b')
      assert.notEqual(result[0], item)
    })
  })

  describe('Maps', () => {
    it('preserves sharing for untouched map values (Requirement A wins)', () => {
      const b = { id: 1 }
      const current = { b, map: new Map([['key', b]]) }
      const result = createPatch(current, (draft: typeof current) => {
        draft.b.id = 2
        void draft.map // Draft map
        // Map entry 'key' is untouched. According to sharedImage theorem,
        // it must resolve to the same finalized identity as draft.b.
        return draft
      })
      // A wins: sharing is preserved
      assert.equal(result.b, result.map.get('key'))
      assert.equal(result.b.id, 2)
      assert.notEqual(result.b, b)
    })

    it('treats setting a map entry to its current value as a SameValue no-op', () => {
      const b = { id: 1 }
      const current = { b, map: new Map([['key', b]]) }
      const result = createPatch(current, (draft: typeof current) => {
        draft.b.id = 2
        void draft.map
        draft.map.set('key', b) // SameValue write: no restoration
        return draft
      })
      assert.equal(result.b, result.map.get('key'))
      assert.equal(result.b.id, 2)
      assert.notEqual(result.b, b)
    })
  })

  describe('Sets', () => {
    it('preserves sharing for untouched Set elements (Requirement A wins)', () => {
      const item = { id: 1 }
      const current = { item, set: new Set([item]) }
      const result = createPatch(current, (draft: typeof current) => {
        draft.item.id = 2
        void draft.set // Draft set
        // Set element is untouched. According to sharedImage theorem,
        // it must resolve to the same finalized identity as draft.item.
        return draft
      })
      const setItem = Array.from(result.set.values())[0]
      // A wins: sharing is preserved
      assert.equal(setItem, result.item)
      assert.equal(result.item.id, 2)
      assert.notEqual(setItem, item)
    })
  })

  describe('Root Auth Return', () => {
    it('honors an explicit root return of current', () => {
      const child = { count: 1 }
      const current = { child }
      const result = createPatch(current, (draft: typeof current) => {
        draft.child.count = 2
        return current
      })
      assert.equal(result, current)
      assert.equal(result.child.count, 1)
    })
  })

  describe('Detachment & Isolation Guarantees', () => {
    it('ensures snapshot(createPatch(...)) is fully detached and keeps shared-image coherence', () => {
      const b = { count: 1 }
      const current = { a: { b }, c: { b } }
      const result = snapshot(
        createPatch(current, (draft: typeof current) => {
          draft.a.b.count = 2
          void draft.c
          draft.c.b = b // SameValue write: no restoration
          return draft
        }),
      ) as typeof current

      assert.notEqual(result.a.b, b)
      assert.notEqual(result.c.b, b)
      assert.equal(result.a.b, result.c.b)
      assert.deepEqual(result.a.b, { count: 2 })
    })
  })
})
