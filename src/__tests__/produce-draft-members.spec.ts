import { assert, describe, it } from 'vitest'
import { produce } from '../index'

// Where a draft decides membership, it compares member identities: a draft counts as the object
// it drafts. lean/Produce/DraftMembers.lean proves the array searches and check-draft-members-runtime.ts compares
// them natively.

describe('array drafts find an object in any of its forms', () => {
  it('removes the item a caller holds', () => {
    const plain = { items: [{ id: 1 }, { id: 2 }] }
    const selected = plain.items[1]
    const result = produce(plain, (draft) => {
      draft.items.splice(draft.items.indexOf(selected), 1)
      return draft
    })
    assert.deepEqual(result.items, [{ id: 1 }])
  })

  it('keeps native results for primitives, holes and fromIndex', () => {
    // eslint-disable-next-line no-sparse-arrays -- a hole, which includes reads as undefined
    const current = { list: [Number.NaN, , 0, 'x'] as unknown[] }
    produce(current, (draft) => {
      assert.isTrue(draft.list.includes(Number.NaN))
      // indexOf compares strictly, so it cannot find NaN, as natively.
      // eslint-disable-next-line use-isnan -- the native result the draft must keep
      assert.equal(draft.list.indexOf(Number.NaN), -1)
      assert.isTrue(draft.list.includes(undefined))
      assert.equal(draft.list.indexOf(undefined), -1)
      assert.equal(draft.list.indexOf(-0), 2)
      assert.equal(draft.list.indexOf('x', 3), 3)
      assert.equal(draft.list.lastIndexOf('x', 2), -1)
      return draft
    })
  })

  it('searches as natively: reads only visited indices, stops at a match, keeps fromIndex', () => {
    let reads = 0
    const list: unknown[] = ['a', 'b', 'c', 'd']
    Object.defineProperty(list, 2, {
      configurable: true,
      enumerable: true,
      get: () => {
        reads += 1
        return 'c'
      },
    })
    const draft = (copy: unknown[], search: (list: unknown[]) => unknown) => {
      const before = reads
      const found = search(copy)
      const native = reads - before
      search(list)
      return { found, nativeReads: reads - before - native, reads: native }
    }
    produce({ list }, (state) => {
      for (const search of [
        (array: unknown[]) => array.includes('b'),
        (array: unknown[]) => array.indexOf('d'),
        (array: unknown[]) => array.indexOf('d', -1),
        (array: unknown[]) => array.lastIndexOf('a'),
        (array: unknown[]) => array.lastIndexOf('a', 1),
        (array: unknown[]) => array.includes('a', Number.POSITIVE_INFINITY),
        (array: unknown[]) => array.lastIndexOf('a', Number.NEGATIVE_INFINITY),
      ]) {
        const result = draft(state.list, search)
        assert.equal(result.found, search(list))
        assert.equal(result.reads, result.nativeReads, String(search))
      }
      return state
    })
  })

  it('leaves other names alone and lets an override run', () => {
    class Tags extends Array<unknown> {
      override includes(): boolean {
        return true
      }
    }
    const current = { list: ['a'], tags: Tags.from(['a']) }
    produce(current, (draft) => {
      assert.equal(String(draft.list), 'a')
      assert.equal(draft.list.constructor, Array)
      assert.equal(Object.getPrototypeOf(draft.list), Array.prototype)
      assert.equal(draft.list.includes.length, 1)
      assert.equal(draft.list.indexOf.name, 'indexOf')
      assert.isTrue(draft.tags.includes('missing'))
      assert.equal(draft.tags.indexOf('a'), 0)
      assert.instanceOf(
        draft.tags.map((tag) => tag),
        Tags,
      )
      return draft
    })
  })

  it('searches a receiver other than the draft as natively', () => {
    produce({ list: ['a'] }, (draft) => {
      assert.equal(draft.list.indexOf.call('abc', 'b'), 1)
      assert.isTrue(draft.list.includes.call({ 0: 'x', length: 1 }, 'x'))
      return draft
    })
  })

  it('cannot change what === compares in recipe code', () => {
    const current = { items: [{ id: 1 }] }
    const selected = current.items[0]
    produce(current, (draft) => {
      assert.isUndefined(draft.items.find((item) => item === selected))
      assert.isDefined(draft.items.find((item) => item.id === selected.id))
      return draft
    })
  })
})
