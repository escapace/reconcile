import { assert, describe, it } from 'vitest'
import { createPatch, patch } from '../index'

describe('draft identity regressions', () => {
  it('unwraps unmodified handles nested in an ordinary replacement', () => {
    const current = { map: new Map([['key', 1]]), set: new Set([2]) }
    const result = createPatch(current, (draft) => ({
      wrapped: { map: draft.map, set: draft.set },
    }))
    assert.equal(result.wrapped.map, current.map)
    assert.equal(result.wrapped.set, current.set)
    assert.deepEqual([...result.wrapped.map], [['key', 1]])
    assert.deepEqual([...result.wrapped.set], [2])
  })

  it('unwraps unchanged array callback results without splitting aliases', () => {
    const child = { count: 1 }
    const current = [child, child]
    const result = createPatch(current, (draft) => draft.map((value) => value))
    assert.notEqual(result, current)
    assert.equal(result[0], child)
    assert.equal(result[1], child)
  })

  it('preserves a cyclic replacement containing an unchanged handle and its base', () => {
    const current = { child: { count: 1 } }
    const result = createPatch(current, (draft) => {
      const replacement: { base: object; handle: object; self?: object } = {
        base: current.child,
        handle: draft.child,
      }
      replacement.self = replacement
      return replacement
    })
    assert.equal(result.self, result)
    assert.equal(result.base, current.child)
    assert.equal(result.handle, current.child)
  })

  it('publishes an unchanged draft collection returned inside a replacement', () => {
    const current = { map: new Map([['key', 1]]) }
    const map = current.map
    const result = patch(current, (draft) => ({ map: draft.map }))
    assert.equal(result, current)
    assert.equal(result.map, map)
    assert.deepEqual([...result.map], [['key', 1]])
  })

  for (const viewFirst of [true, false]) {
    for (const changed of [true, false]) {
      it(`preserves buffer aliases (view first: ${viewFirst}, changed: ${changed})`, () => {
        const buffer = new ArrayBuffer(2)
        const current = { buffer, typed: new Uint8Array(buffer), view: new DataView(buffer) }
        const result = createPatch(current, (draft) => {
          if (viewFirst) {
            void draft.view
            void draft.typed
            void draft.buffer
          } else {
            void draft.buffer
            void draft.typed
            void draft.view
          }
          assert.equal(draft.view.buffer, draft.buffer)
          assert.equal(draft.typed.buffer, draft.buffer)
          if (changed) {
            draft.typed[0] = 7
          }
          return draft
        })
        assert.equal(result.typed.buffer, result.buffer)
        assert.equal(result.view.buffer, result.buffer)
        assert.equal(new Uint8Array(result.buffer)[0], changed ? 7 : 0)
        if (!changed) {
          assert.equal(result.buffer, current.buffer)
          assert.equal(result.view, current.view)
          assert.equal(result.typed, current.typed)
        }
        assert.equal(new Uint8Array(current.buffer)[0], 0)
      })
    }
  }

  for (const changed of [true, false]) {
    it(`finalizes a buffer obtained directly from a view (changed: ${changed})`, () => {
      const current = new Uint8Array([0])
      const result = createPatch(current, (draft) => {
        if (changed) {
          draft[0] = 7
        }
        return { buffer: draft.buffer, view: draft }
      })
      assert.equal(result.buffer, result.view.buffer)
      assert.equal(result.view[0], changed ? 7 : 0)
      if (!changed) {
        assert.equal(result.buffer, current.buffer)
        assert.equal(result.view, current)
      }
    })
  }

  it('reuses an unchanged special clone after assigning it to another property', () => {
    const current: { a: Date; b: Date | null } = { a: new Date(0), b: null }
    const result = createPatch(current, (draft) => {
      draft.b = draft.a
      assert.equal(draft.a, draft.b)
      return draft
    })
    assert.equal(result.a, current.a)
    assert.equal(result.b, current.a)
    assert.equal(current.b, null)
  })

  it('keeps a reassigned Date clone shared while reading and mutating it', () => {
    const current: { a: Date; b: Date | null } = { a: new Date(0), b: null }
    const result = createPatch(current, (draft) => {
      draft.b = draft.a
      assert.equal(draft.b, draft.a)
      draft.b.setTime(9)
      return draft
    })
    assert.equal(result.a, result.b)
    assert.equal(result.a.getTime(), 9)
    assert.equal(current.a.getTime(), 0)
  })

  it('keeps a reassigned typed-array clone shared through an array and a map', () => {
    const current = {
      array: [] as Uint8Array[],
      map: new Map<string, Uint8Array>(),
      typed: new Uint8Array([0]),
    }
    const result = createPatch(current, (draft) => {
      draft.array.push(draft.typed)
      draft.map.set('typed', draft.typed)
      assert.equal(draft.array[0], draft.typed)
      assert.equal(draft.map.get('typed'), draft.typed)
      draft.array[0][0] = 9
      return draft
    })
    assert.equal(result.array[0], result.typed)
    assert.equal(result.map.get('typed'), result.typed)
    assert.equal(result.typed[0], 9)
    assert.equal(current.typed[0], 0)
  })

  // Read the exact inherited function identity without invoking it as an unbound method.
  const inheritedToString = Object.getOwnPropertyDescriptor(Object.prototype, 'toString')!
    .value as () => string

  it('creates an own property when the assigned value equals an inherited value', () => {
    const current = {}
    const result = createPatch(current, (draft) => {
      draft.toString = inheritedToString
      return draft
    })
    assert.equal(Object.hasOwn(result, 'toString'), true)
    assert.equal(Object.hasOwn(current, 'toString'), false)
    assert.equal(
      Object.getOwnPropertyDescriptor(result, 'toString')?.value as unknown,
      inheritedToString,
    )
  })

  it('re-adds an own property whose value equals the inherited value', () => {
    const current = { toString: inheritedToString }
    const result = createPatch(current, (draft) => {
      Reflect.deleteProperty(draft, 'toString')
      draft.toString = inheritedToString
      return draft
    })
    assert.equal(Object.hasOwn(result, 'toString'), true)
    assert.notEqual(result, current)
  })

  it('keeps a same-value write to an existing own property a no-op', () => {
    const current = { toString: inheritedToString }
    assert.equal(
      createPatch(current, (draft) => {
        draft.toString = inheritedToString
        return draft
      }),
      current,
    )
  })

  for (const timestamp of [0, Number.NaN]) {
    it(`reuses an unchanged Date root with timestamp ${timestamp}`, () => {
      const current = new Date(timestamp)
      assert.equal(
        createPatch(current, (draft) => draft),
        current,
      )
    })
  }

  it('publishes transitions between valid and invalid Date values', () => {
    const valid = new Date(0)
    const invalid = createPatch(valid, (draft) => {
      draft.setTime(Number.NaN)
      return draft
    })
    assert.notEqual(invalid, valid)
    assert.equal(Number.isNaN(invalid.getTime()), true)
    const result = createPatch(invalid, (draft) => {
      draft.setTime(1)
      return draft
    })
    assert.notEqual(result, invalid)
    assert.equal(result.getTime(), 1)
  })
})
