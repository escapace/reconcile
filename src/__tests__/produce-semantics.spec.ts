import { assert, describe, it } from 'vitest'

import { produce } from '../produce'
import { firstMapEntry } from './fixtures/contents'

describe('produce semantics', () => {
  it('returns the original current value when no changes are made', () => {
    const current = {
      aProp: 'hi',
      nested: {
        value: 1,
      },
    }

    const result = produce(current, (draft) => {
      assert.equal(draft.aProp, 'hi')
      assert.equal(draft.nested.value, 1)
      return draft
    })

    assert.equal(result, current)
  })

  it('returns the original current value when an existing field is assigned the same value', () => {
    const current = {
      aProp: 'hi',
      nested: {
        value: 1,
      },
    }

    const result = produce(current, (draft) => {
      draft.aProp = 'hi'
      draft.nested.value = 1
      return draft
    })

    assert.equal(result, current)
  })

  it('does structural sharing for unchanged siblings when one path changes', () => {
    const current = {
      changed: { value: 1 },
      unchanged: { keep: true },
    }

    const result = produce(current, (draft) => {
      draft.changed.value = 2
      return draft
    })

    assert.notEqual(result, current)
    assert.notEqual(result.changed, current.changed)
    assert.equal(result.unchanged, current.unchanged)
    assert.deepEqual(result, {
      changed: { value: 2 },
      unchanged: { keep: true },
    })
    assert.deepEqual(current, {
      changed: { value: 1 },
      unchanged: { keep: true },
    })
  })

  it('returns the original current value when deleting a nonexisting property', () => {
    const current = {
      aProp: 'hi',
    }

    const result = produce(current, (draft) => {
      delete (draft as { missing?: boolean } & typeof draft).missing
      return draft
    })

    assert.equal(result, current)
  })

  it('returns the original current value when assigning an existing undefined field to undefined', () => {
    const current: {
      value: undefined
    } = {
      value: undefined,
    }

    const result = produce(current, (draft) => {
      draft.value = undefined
      return draft
    })

    assert.equal(result, current)
    assert.equal('value' in result, true)
  })

  it('creates a present property when assigning a new undefined field', () => {
    const current: {
      added?: undefined
    } = {}

    const result = produce(current, (draft) => {
      draft.added = undefined
      return draft
    })

    assert.notEqual(result, current)
    assert.equal('added' in result, true)
    assert.equal(result.added, undefined)
  })

  it('finalizes add-then-delete of the same property and restores identity', () => {
    const current = {
      nested: {
        value: 1,
      },
    }

    const result = produce(current, (draft) => {
      ;(draft.nested as { extra?: boolean } & typeof draft.nested).extra = true
      delete (draft.nested as { extra?: boolean } & typeof draft.nested).extra
      return draft
    })

    assert.equal(result, current)
    assert.equal(result.nested, current.nested)
    assert.deepEqual(result, { nested: { value: 1 } })
    assert.equal('extra' in result.nested, false)
  })

  it('finalizes delete-then-reassign of the same reference and restores identity', () => {
    const shared = { value: 1 }
    const current: {
      child?: { value: number }
    } = {
      child: shared,
    }

    const result = produce(current, (draft) => {
      const child = draft.child as { value: number }
      delete draft.child
      draft.child = child
      return draft
    })

    assert.equal(result, current)
    assert.equal(result.child, shared)
  })

  it('leaves the draft untouched when reading a child and writing the original reference back', () => {
    // Assigning the same reference that is already visible through the draft is a SameValue
    // no-op write and never marks the draft modified.
    const child = { value: 1 }
    const current = { child }

    const result = produce(current, (draft) => {
      void draft.child
      draft.child = child
      return draft
    })

    assert.equal(result, current)
  })

  it('keeps child-draft mutations sticky even when the parent receives a SameValue write back', () => {
    // Mutating a child through its draft handle permanently marks that child modified. A later
    // SameValue write of the original reference at the parent level does not discard the child
    // mutation, so the finalized next value reflects the child change coherently.
    const child = { value: 1 }
    const current = { child }

    const result = produce(current, (draft) => {
      const childDraft = draft.child
      childDraft.value = 2
      draft.child = child
      return draft
    })

    assert.notEqual(result, current)
    assert.notEqual(result.child, child)
    assert.equal(result.child.value, 2)
    assert.deepEqual(current, { child: { value: 1 } })
  })

  it('keeps child-draft mutations when the mutated child is kept in the result', () => {
    const child = { value: 1 }
    const current = { child }

    const result = produce(current, (draft) => {
      const childDraft = draft.child
      childDraft.value = 2
      draft.child = child
      draft.child = childDraft
      return draft
    })

    assert.notEqual(result, current)
    assert.notEqual(result.child, child)
    assert.deepEqual(result, { child: { value: 2 } })
    assert.deepEqual(current, { child: { value: 1 } })
  })

  it('preserves out-of-range array assignment shape', () => {
    const current: string[] = []

    const result = produce(current, (draft) => {
      draft[2] = 'v2'
      return draft
    })

    assert.equal(result.length, 3)
    assert.deepEqual(result, [undefined, undefined, 'v2'])
    assert.equal(0 in result, false)
    assert.equal(1 in result, false)
    assert.equal(2 in result, true)
  })

  it('stores undefined as a present map value for a new key', () => {
    const current = new Map<string, undefined>()

    const result = produce(current, (draft) => {
      draft.set('key', undefined)
      return draft
    })

    assert.notEqual(result, current)
    assert.equal(result.has('key'), true)
    assert.equal(result.get('key'), undefined)
  })

  it('returns the original current map when setting an existing key to the same value', () => {
    const current = new Map<string, number>([['key', 1]])

    const result = produce(current, (draft) => {
      draft.set('key', 1)
      return draft
    })

    assert.equal(result, current)
  })

  it('restores a draft-originating map key after mutate-then-mutate-back on the key', () => {
    const key = { label: 'key' }
    const current = {
      key,
      map: new Map<object, number>([[key, 1]]),
    }

    const result = produce(current, (draft) => {
      draft.key.label = 'updated'
      draft.key.label = 'key'
      return draft.map
    })

    assert.equal(result, current.map)
    assert.equal(firstMapEntry(result)[0], current.key)
    assert.equal((firstMapEntry(result)[0] as { label: string }).label, 'key')
    assert.equal(result.get(firstMapEntry(result)[0]), 1)
    assert.equal(current.key.label, 'key')
  })

  it('restores draft identity after mutate-then-mutate-back on a nested property', () => {
    const current = {
      nested: {
        value: 1,
      },
    }

    const result = produce(current, (draft) => {
      draft.nested.value = 2
      draft.nested.value = 1
      return draft
    })

    assert.equal(result, current)
    assert.equal(result.nested, current.nested)
    assert.deepEqual(result, { nested: { value: 1 } })
  })
})
