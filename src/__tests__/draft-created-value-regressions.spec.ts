import { assert, describe, it } from 'vitest'
import { createPatch } from '../index'

describe('values created and reused inside recipes', () => {
  for (const nested of [false, true]) {
    for (const changed of [false, true]) {
      for (const dataView of [false, true]) {
        it(`preserves new views over draft buffers (nested: ${nested}, changed: ${changed}, DataView: ${dataView})`, () => {
          const current = {
            a: new Uint8Array(4),
            box: {
              unread: undefined as DataView | Uint8Array | undefined,
              view: undefined as DataView | Uint8Array | undefined,
            },
            view: undefined as DataView | Uint8Array | undefined,
          }
          const result = createPatch(current, (draft) => {
            const view = dataView ? new DataView(draft.a.buffer, 1, 2) : draft.a.subarray(1, 3)
            if (nested) draft.box = { unread: view, view }
            else draft.view = view
            const read = nested ? draft.box.view! : draft.view!
            assert.equal(read.buffer, draft.a.buffer)
            if (changed) {
              if (read instanceof DataView) read.setUint8(0, 9)
              else read[0] = 9
              assert.equal(draft.a[1], 9)
            }
            return draft
          })
          const view = nested ? result.box.view! : result.view!
          assert.equal(view.buffer, result.a.buffer)
          if (nested) assert.equal(result.box.unread, view)
          assert.equal(view.byteOffset, 1)
          assert.equal(view.byteLength, 2)
          assert.equal(result.a[1], changed ? 9 : 0)
          assert.equal(current.a[1], 0)
          if (!changed) assert.equal(result.a, current.a)
        })
      }
    }
  }

  for (const useBase of [false, true]) {
    it(`resolves keys already stored as draft handles (lookup by base: ${useBase})`, () => {
      const current = { key: { count: 0 }, map: new Map<object, number>() }
      const result = createPatch(current, (draft) => {
        draft.map = new Map([[draft.key, 1]])
        const key = useBase ? current.key : draft.key
        assert.isTrue(draft.map.has(key))
        assert.equal(draft.map.get(key), 1)
        draft.map.set(key, 2)
        assert.equal(draft.map.size, 1)
        assert.equal(draft.map.get(key), 2)
        assert.isTrue(draft.map.delete(key))
        assert.equal(draft.map.size, 0)
        assert.isFalse(draft.map.delete(key))
        draft.map.set(key, 3)
        draft.key.count = 1
        return draft
      })
      assert.equal(result.map.size, 1)
      assert.equal(result.map.get(result.key), 3)
      assert.equal(current.key.count, 0)
      assert.equal(current.map.size, 0)
    })
  }

  for (const reverse of [false, true]) {
    for (const value of [
      new Date(1),
      new ArrayBuffer(2),
      new DataView(new ArrayBuffer(2)),
      new Uint8Array(2),
    ]) {
      it(`preserves unchanged special aliases across replacement paths (${Object.prototype.toString.call(value)}, reverse: ${reverse})`, () => {
        const current = { nested: { value } }
        const result = createPatch(current, (draft) => {
          void draft.nested.value
          return reverse
            ? { nested: current.nested, value }
            : { ...{ value }, nested: current.nested }
        })
        assert.equal(result.value, result.nested.value)
        assert.equal(result.value, value)
      })
    }
  }
})
