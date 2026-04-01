import { assert, describe, it } from 'vitest'

import { createPatch } from '../patch'

describe('nested authoritative finalization coherence regressions', () => {
  it('finalizes a nested plain-object draft root when a shared descendant changed elsewhere', () => {
    const shared = { count: 1 }
    const current = {
      left: { shared },
      right: { shared },
    }

    const result = createPatch(current, (draft) => {
      void draft.right
      draft.left.shared.count = 2
      return draft.right
    })

    assert.notEqual(result, current.right)
    assert.notEqual(result.shared, shared)
    assert.equal(result.shared.count, 2)
    assert.equal(current.right.shared.count, 1)
  })

  it('finalizes a nested array draft root when a shared element changed elsewhere', () => {
    const shared = { count: 1 }
    const current = {
      left: { shared },
      right: [shared],
    }

    const result = createPatch(current, (draft) => {
      void draft.right
      draft.left.shared.count = 2
      return draft.right
    })

    assert.notEqual(result, current.right)
    assert.notEqual(result[0], shared)
    assert.equal(result[0].count, 2)
    assert.equal(current.right[0].count, 1)
  })

  it('finalizes a nested draft handle inside an ordinary returned root when a shared descendant changed elsewhere', () => {
    const shared = { count: 1 }
    const current = {
      left: { shared },
      right: { shared },
    }

    const result = createPatch(current, (draft) => {
      draft.left.shared.count = 2
      return { wrapped: draft.right }
    }) as {
      wrapped: { shared: { count: number } }
    }

    assert.notEqual(result.wrapped, current.right)
    assert.notEqual(result.wrapped.shared, shared)
    assert.equal(result.wrapped.shared.count, 2)
    assert.equal(current.right.shared.count, 1)
  })

  it('finalizes clone-on-read specials reachable through a nested plain-object draft root', () => {
    const date = new Date('2024-01-01T00:00:00.000Z')
    const current = {
      left: date,
      right: { date },
    }

    const result = createPatch(current, (draft) => {
      draft.left.setUTCFullYear(2025)
      return draft.right
    })

    assert.notEqual(result, current.right)
    assert.notEqual(result.date, date)
    assert.equal(result.date.getUTCFullYear(), 2025)
    assert.equal(current.right.date.getUTCFullYear(), 2024)
  })

  it('finalizes a nested map draft root coherently when a shared value changed elsewhere', () => {
    const shared = { id: 1 }
    const current = {
      map: new Map<string, { id: number }>([['key', shared]]),
      shared,
    }

    const result = createPatch(current, (draft) => {
      draft.shared.id = 2
      draft.map.set('key', shared) // SameValue write: no restoration
      return draft.map
    })

    assert.notEqual(result, current.map)
    assert.notEqual(result.get('key'), shared)
    assert.equal(result.get('key')!.id, 2)
    assert.equal(current.map.get('key')!.id, 1)
  })
})
