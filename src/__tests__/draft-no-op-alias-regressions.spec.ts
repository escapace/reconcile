import { assert, describe, it } from 'vitest'
import { createPatch } from '../index'

describe('draft no-op and unread alias regressions', () => {
  for (const dataView of [false, true]) {
    for (const changed of [false, true]) {
      it(`preserves unread nested buffer aliases (DataView: ${dataView}, changed: ${changed})`, () => {
        const buffer = new ArrayBuffer(4)
        const view = dataView ? new DataView(buffer, 1, 2) : new Uint8Array(buffer, 1, 2)
        const current = {
          array: [view],
          map: new Map([[view, view]]),
          object: { view },
          set: new Set([view]),
          writer: new Uint8Array(buffer),
        }
        const result = createPatch(current, (draft) => {
          if (changed) {
            draft.writer[1] = 9
          } else {
            void draft.writer
          }
          return draft
        })
        const views = [
          result.array[0],
          ...result.map.keys(),
          ...result.map.values(),
          result.object.view,
          ...result.set,
        ]
        for (const actual of views) {
          assert.equal(actual.buffer, result.writer.buffer)
          assert.equal(actual.byteOffset, 1)
          assert.equal(actual.byteLength, 2)
          assert.equal(new Uint8Array(actual.buffer)[1], changed ? 9 : 0)
          assert.equal(actual, result.array[0])
          if (!changed) assert.equal(actual, view)
        }
        assert.equal(new Uint8Array(buffer)[1], 0)
      })
    }
  }

  for (const child of [{ count: 1 }, [1], new Map([['key', 1]]), new Set([1])]) {
    it(`treats ${Object.prototype.toString.call(child)} handle write-backs as no-ops`, () => {
      const current = { child }
      assert.equal(
        createPatch(current, (draft) => {
          const handle = draft.child
          draft.child = handle
          return draft
        }),
        current,
      )
      const map = new Map([['key', child]])
      assert.equal(
        createPatch(map, (draft) => {
          draft.set('key', draft.get('key')!)
          return draft
        }),
        map,
      )
      const array = [child]
      assert.equal(
        createPatch(array, (draft) => draft.copyWithin(0, 0)),
        array,
      )
    })
  }

  it('retains child mutations when its handle is written back', () => {
    const current = { child: { count: 1 } }
    const result = createPatch(current, (draft) => {
      draft.child.count = 2
      const handle = draft.child
      draft.child = handle
      return draft
    })
    assert.notEqual(result, current)
    assert.deepEqual(result, { child: { count: 2 } })
    assert.equal(current.child.count, 1)
    const map = new Map([['key', current.child]])
    const nextMap = createPatch(map, (draft) => {
      const child = draft.get('key')!
      child.count = 2
      draft.set('key', child)
      return draft
    })
    assert.notEqual(nextMap, map)
    assert.deepEqual(nextMap.get('key'), { count: 2 })
    assert.equal(current.child.count, 1)
  })

  it('keeps real replacements and their reversals modified', () => {
    const current = { child: { count: 1 }, other: { count: 1 } }
    const result = createPatch(current, (draft) => {
      const child = draft.child
      draft.child = draft.other
      draft.child = child
      return draft
    })
    assert.notEqual(result, current)
    assert.equal(result.child, current.child)
    const replacement = createPatch(current, (draft) => {
      draft.child = draft.other
      return draft
    })
    assert.equal(replacement.child, current.other)
  })

  it('does not mark inherited or missing deletions as changes', () => {
    const current = {}
    assert.equal(
      createPatch(current, (draft) => {
        assert.isTrue(Reflect.deleteProperty(draft, 'toString'))
        assert.isTrue(Reflect.deleteProperty(draft, 'missing'))
        return draft
      }),
      current,
    )
    const array = new Array<unknown>(2)
    assert.equal(
      createPatch(array, (draft) => {
        assert.isTrue(Reflect.deleteProperty(draft, 'map'))
        assert.isTrue(Reflect.deleteProperty(draft, '0'))
        return draft
      }),
      array,
    )
  })

  it('still removes own properties that shadow inherited properties', () => {
    const current = { toString: 1 }
    const result = createPatch(current, (draft) => {
      Reflect.deleteProperty(draft, 'toString')
      return draft
    })
    assert.notEqual(result, current)
    assert.isFalse(Object.hasOwn(result, 'toString'))
    assert.equal(current.toString, 1)
  })
})
