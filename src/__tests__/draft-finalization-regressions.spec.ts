import { assert, describe, it } from 'vitest'

import { createPatch } from '../patch'

class MutableClass {
  value = 5
}

describe('draft finalization regressions', () => {
  it('preserves self-references and shared descendants during root finalization', () => {
    interface SelfReference {
      count: number
      self?: SelfReference
    }

    const current: SelfReference = { count: 0 }
    current.self = current

    const result = createPatch(current, (draft) => {
      draft.count = 1
      return draft
    })

    assert.notEqual(result, current)
    assert.equal(result.self, result)
    assert.equal(result.count, 1)
    assert.equal(current.count, 0)
  })

  it('does not freeze class instances or typed arrays when drafting adjacent state', () => {
    const current = {
      mutableClass: new MutableClass(),
      someValue: 5,
      typedArray: new Uint8Array(10),
    }

    const result = createPatch(current, (draft) => {
      draft.someValue = 6
      return draft
    })

    assert.doesNotThrow(() => {
      current.mutableClass.value = 6
      current.typedArray[0] = 1
    })

    assert.equal(Object.isFrozen(current.mutableClass), false)
    assert.equal(Object.isFrozen(current.typedArray), false)
    assert.equal(result.someValue, 6)
  })

  it('keeps array callback items draft-wrapped when mutating through non-mutating array methods', () => {
    const current = [{ count: 0 }, { count: 1 }]

    const result = createPatch(current, (draft) => {
      draft.filter((item) => {
        if (item.count === 0) {
          item.count = 2
        }

        return true
      })

      return draft
    })

    assert.equal(current[0].count, 0)
    assert.equal(result[0].count, 2)
    assert.equal(result[1], current[1])
  })

  it('finalizes draft sets nested in new map values', () => {
    const base = {
      map: new Map<string, { users: Set<{ name: string }> }>([['key1', { users: new Set() }]]),
    }

    const state1 = createPatch(base, (draft) => {
      draft.map.get('key1')!.users.add({ name: 'user1' })
      return draft
    })

    const state2 = createPatch(state1, (draft) => {
      const existingUsers = draft.map.get('key1')?.users ?? new Set<{ name: string }>()
      const newEntry = { users: existingUsers }
      draft.map.set('key1', newEntry)
      newEntry.users.add({ name: 'user2' })
      return draft
    })

    const users = state2.map.get('key1')!.users
    assert.equal(users instanceof Set, true)
    assert.deepEqual(
      Array.from(users, (user) => user.name),
      ['user1', 'user2'],
    )
  })

  it('finalizes plain set members that contain nested draft handles', () => {
    const result = createPatch(
      {
        items: [{ id: 1, name: 'item1' }],
        itemSet: new Set<{ extra: string; item: { id: number; name: string } }>(),
      },
      (draft) => {
        const draftItem = draft.items[0]
        const wrapper = { extra: 'wrapper data', item: draftItem }
        draft.itemSet.add(wrapper)
        draftItem.name = 'modified'
        return draft
      },
    )

    assert.deepEqual(Array.from(result.itemSet), [
      { extra: 'wrapper data', item: { id: 1, name: 'modified' } },
    ])
  })

  it('finalizes deeply nested draft handles inside plain set members', () => {
    const result = createPatch(
      {
        items: [{ id: 1, name: 'item1' }],
        itemSet: new Set<{ level1: { level2: { item: { id: number; name: string } } } }>(),
      },
      (draft) => {
        const draftItem = draft.items[0]
        draft.itemSet.add({ level1: { level2: { item: draftItem } } })
        draftItem.name = 'modified'
        return draft
      },
    )

    assert.deepEqual(Array.from(result.itemSet), [
      { level1: { level2: { item: { id: 1, name: 'modified' } } } },
    ])
  })

  it('finalizes nested draft handles in values inserted with mutating array methods', () => {
    const pushed = createPatch([{ nestedArray: [] as number[] }], (draft) => {
      draft.push({ ...draft[0] })
      return draft
    })
    assert.deepEqual(pushed[0].nestedArray, [])
    assert.deepEqual(pushed[1].nestedArray, [])

    const pushedDraft = createPatch([{ nestedArray: [] as number[] }], (draft) => {
      draft.push(draft[0])
      return draft
    })
    assert.equal(pushedDraft[0], pushedDraft[1])
    assert.deepEqual(pushedDraft[1].nestedArray, [])

    const pushedNestedObject = createPatch([{ nested: { value: 42 } }], (draft) => {
      draft.push({ ...draft[0] })
      return draft
    })
    assert.deepEqual(pushedNestedObject[1].nested, { value: 42 })

    const unshifted = createPatch([{ nestedArray: [1] }], (draft) => {
      draft.unshift({ ...draft[0] })
      return draft
    })
    assert.deepEqual(unshifted[0].nestedArray, [1])
    assert.deepEqual(unshifted[1].nestedArray, [1])

    const spliced = createPatch([{ nestedArray: ['a', 'b'] }], (draft) => {
      draft.splice(0, 0, { ...draft[0] })
      return draft
    })
    assert.deepEqual(spliced[0].nestedArray, ['a', 'b'])
    assert.deepEqual(spliced[1].nestedArray, ['a', 'b'])
  })
})
