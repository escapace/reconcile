import { deepSignal } from 'alien-deepsignals'
import { assert, describe, it } from 'vitest'
import { isReactive, reactive } from 'vue'

import { createPatch, patch, reconcile, snapshot } from '../index'

const bytesOfArrayBuffer = (value: ArrayBufferLike): number[] => Array.from(new Uint8Array(value))
const returnFortyTwo = (): number => 42

describe('README publication semantics', () => {
  describe('next-value construction and publication', () => {
    it('createPatch computes a next value without publishing it', () => {
      const current = {
        changed: { count: 0 },
        untouched: { keep: true },
      }

      const next = createPatch(current, (draft) => {
        draft.changed.count = 1
        return draft
      })

      assert.deepEqual(current, {
        changed: { count: 0 },
        untouched: { keep: true },
      })
      assert.deepEqual(next, {
        changed: { count: 1 },
        untouched: { keep: true },
      })
      assert.notEqual(next, current)
    })

    it('patch publishes onto the existing object graph when compatible', () => {
      const nested = { count: 0 }
      const current = {
        nested,
        sibling: { keep: true },
      }
      const siblingReference = current.sibling

      const result = patch(current, (draft) => {
        draft.nested.count = 1
        return draft
      })

      assert.equal(result, current)
      assert.equal(result.nested, nested)
      assert.equal(result.sibling, siblingReference)
      assert.equal(result.nested.count, 1)
    })

    it('reconcile publishes onto the existing object graph when compatible', () => {
      const child = { count: 0 }
      const current = { child }
      const next = { child: { count: 2 } }

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal(result.child, child)
      assert.equal(result.child.count, 2)
    })
  })

  describe('matching rules by value kind', () => {
    it('replaces changed primitives and keeps functions by reference', () => {
      const current = { fn: (): number => 0 }
      const next = { fn: returnFortyTwo }

      assert.equal(reconcile(1, 2), 2)

      const result = reconcile(current, next) as { fn: () => number }
      const detached = snapshot(result) as { fn: () => number }

      assert.equal(result.fn, returnFortyTwo)
      assert.equal(detached.fn, returnFortyTwo)
    })

    it('matches plain objects by property key and uses the next own-key order', () => {
      const x = { id: 'x' }
      const y = { id: 'y' }
      const current = { a: x, b: y }
      // eslint-disable-next-line perfectionist/sort-objects
      const next = { b: x, a: y }

      const result = reconcile(current, next) as { a: typeof x; b: typeof y }

      assert.equal(result, current)
      assert.equal(result.a, x)
      assert.equal(result.b, y)
      assert.deepEqual(Object.keys(result), ['b', 'a'])
      assert.equal(result.a.id, 'y')
      assert.equal(result.b.id, 'x')
    })

    it('matches arrays by index, including reorder, length, and sparse holes', () => {
      const a = { id: 'a' }
      const b = { id: 'b' }
      const current = [a, b, { id: 'drop' }] as Array<{ id: string } | undefined>
      const next = [b, a] as Array<{ id: string } | undefined>
      next.length = 4

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal(result[0], a)
      assert.equal(result[1], b)
      assert.equal(result[0]!.id, 'b')
      assert.equal(result[1]!.id, 'a')
      assert.equal(result.length, 4)
      assert.equal(2 in result, false)
      assert.equal(3 in result, false)
      assert.equal(result[3], undefined)
    })

    it('matches maps by entry order and iterates in the next order', () => {
      const first = { id: 'first' }
      const second = { id: 'second' }
      const current = new Map<string, { id: string }>([
        ['left', first],
        ['right', second],
      ])
      /* eslint-disable perfectionist/sort-maps */
      const next = new Map<string, { id: string }>([
        ['right', second],
        ['left', first],
      ])
      /* eslint-enable perfectionist/sort-maps */

      const result = reconcile(current, next)
      const entries = [...result.entries()]

      assert.equal(entries[0][1], first)
      assert.equal(entries[1][1], second)
      assert.deepEqual(
        entries.map(([key, value]) => [key, value.id]),
        [
          ['right', 'second'],
          ['left', 'first'],
        ],
      )
    })

    it('matches sets by entry order and iterates in the next order', () => {
      const a = { id: 'a' }
      const b = { id: 'b' }
      const current = new Set([a, b])
      // eslint-disable-next-line perfectionist/sort-sets
      const next = new Set([b, a])

      const result = reconcile(current, next)
      const values = [...result]

      assert.equal(values[0], a)
      assert.equal(values[1], b)
      assert.deepEqual(
        values.map((value) => value.id),
        ['b', 'a'],
      )
    })

    it('matches Date values by time and preserves sharing when next shares one Date', () => {
      const sharedNextDate = new Date('2025-01-01T00:00:00.000Z')
      const current = {
        left: new Date('2024-01-01T00:00:00.000Z'),
        right: new Date('2024-06-01T00:00:00.000Z'),
      }
      const next = {
        left: sharedNextDate,
        right: sharedNextDate,
      }

      const result = reconcile(current, next)

      assert.equal(result.left, result.right)
      assert.equal(result.left.getTime(), sharedNextDate.getTime())
    })

    it('matches buffers and views by bytes, view type, and shared backing buffer', () => {
      const current = {
        buffer: new Uint8Array([0, 0, 0, 0]).buffer,
        typed: new Uint8Array([9, 9, 9, 9]),
        view: new DataView(new Uint8Array([8, 8, 8, 8]).buffer),
      }
      const nextBuffer = new Uint8Array([5, 6, 7, 8]).buffer
      const next = {
        buffer: nextBuffer,
        typed: new Uint16Array(nextBuffer),
        view: new DataView(nextBuffer, 1, 2),
      }

      const result = reconcile(current, next) as {
        buffer: ArrayBuffer
        typed: Uint16Array | Uint8Array
        view: DataView
      }

      assert.deepEqual(bytesOfArrayBuffer(result.buffer), [5, 6, 7, 8])
      assert.equal(result.typed.constructor, Uint16Array)
      assert.equal(result.typed.buffer, result.buffer)
      assert.equal(result.view.buffer, result.buffer)
      assert.equal(result.view.byteOffset, 1)
      assert.equal(result.view.byteLength, 2)
    })
  })

  describe('whole-value behavior', () => {
    it('keeps shared references shared when the next value shares one object', () => {
      const shared = { value: 1 }
      const current = {
        left: { value: 0 },
        right: { value: 0 },
      }
      const next = {
        left: shared,
        right: shared,
      }

      const result = reconcile(current, next) as { left: object; right: object }

      assert.equal(result.left, result.right)
    })

    it('keeps distinct references distinct when the next value uses two equal-looking objects', () => {
      const currentShared = { value: 0 }
      const current = {
        left: currentShared,
        right: currentShared,
      }
      const next = {
        left: { value: 1 },
        right: { value: 1 },
      }

      const result = reconcile(current, next) as {
        left: { value: number }
        right: { value: number }
      }

      assert.notEqual(result.left, result.right)
      assert.deepEqual(result, next)
    })

    it('preserves cycles', () => {
      const current: { value: number; self?: unknown } = { value: 0 }
      current.self = current

      const next: { value: number; self?: unknown } = { value: 1 }
      next.self = next

      const result = reconcile(current, next) as typeof current

      assert.equal(result, current)
      assert.equal(result.self, result)
      assert.equal(result.value, 1)
    })

    it('makes buffer and view sharing follow the next value, including separation', () => {
      const sharedBuffer = new Uint8Array([1, 2, 3, 4]).buffer
      const current = {
        buffer: sharedBuffer,
        view: new DataView(sharedBuffer),
      }
      const next = {
        buffer: new Uint8Array([5, 6, 7, 8]).buffer,
        view: new DataView(new Uint8Array([9, 10, 11, 12]).buffer),
      }

      const result = reconcile(current, next) as typeof current

      assert.notEqual(result.view.buffer, result.buffer)
      assert.deepEqual(bytesOfArrayBuffer(result.buffer), [5, 6, 7, 8])
      assert.deepEqual(
        bytesOfArrayBuffer(result.view.buffer).slice(
          result.view.byteOffset,
          result.view.byteOffset + result.view.byteLength,
        ),
        [9, 10, 11, 12],
      )
    })

    it('returns a finalized but not detached value from createPatch, and snapshot detaches it', () => {
      const untouched = { keep: true }
      const current = {
        changed: { count: 0 },
        untouched,
      }

      const next = createPatch(current, (draft) => {
        draft.changed.count = 1
        return draft
      })
      const detached = snapshot(next) as typeof next

      assert.notEqual(next, current)
      assert.notEqual(next.changed, current.changed)
      assert.equal(next.untouched, untouched)
      assert.equal(current.changed.count, 0)

      assert.notEqual(detached.changed, next.changed)
      assert.notEqual(detached.untouched, untouched)
      assert.deepEqual(detached, next)
    })
  })

  describe('wrapper compatibility', () => {
    it('applies the same identity-reuse rules to Vue reactive proxies', () => {
      const current = reactive({
        nested: { count: 0 },
        sibling: { keep: true },
      })
      const nestedReference = current.nested
      const siblingReference = current.sibling

      const result = patch(current, (draft) => {
        draft.nested.count = 4
        return draft
      })

      assert.equal(result, current)
      assert.equal(isReactive(result), true)
      assert.equal(result.nested, nestedReference)
      assert.equal(result.sibling, siblingReference)
      assert.equal(result.nested.count, 4)
    })

    it('applies the same identity-reuse rules to alien-deepsignals objects', () => {
      const current = deepSignal({
        nested: { count: 0 },
        sibling: { keep: true },
      })
      const siblingReference = current.sibling

      const result = patch(current, (draft) => {
        draft.nested.count = 5
        return draft
      })

      assert.equal(result, current)
      assert.equal(result.sibling, siblingReference)
      assert.equal(result.nested.count, 5)
    })
  })
})
