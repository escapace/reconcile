import { assert, describe, it } from 'vitest'

import { createPatch, patch } from '../patch'

const firstSetEntry = <T>(value: Set<T>): T => value.values().next().value!
const firstMapEntry = <K, V>(value: Map<K, V>): readonly [K, V] => value.entries().next().value!
const bytesOf = (value: ArrayBufferLike): number[] => Array.from(new Uint8Array(value))

describe('patch no-restoration comprehensive semantics', () => {
  describe('reads and SameValue no-op writes stay unchanged', () => {
    it('keeps a plain-object draft on current for pure reads, SameValue writes, and deleting a missing property', () => {
      const current: {
        child: { count: number }
        missing?: boolean
      } = {
        child: { count: 1 },
      }

      const result = createPatch(current, (draft) => {
        void draft.child
        draft.child.count = 1
        delete draft.missing
        return draft
      })

      assert.equal(result, current)
      assert.equal(result.child, current.child)
    })

    it('keeps an array draft on current for pure reads, SameValue writes, and deleting an existing hole', () => {
      const current = [1, 2, 3] as Array<number | undefined>
      Reflect.deleteProperty(current, 1)

      const result = createPatch(current, (draft) => {
        void draft[0]
        draft[0] = 1
        Reflect.deleteProperty(draft, 1)
        return draft
      })

      assert.equal(result, current)
      assert.equal(result.length, 3)
      assert.equal(1 in result, false)
    })

    it('keeps a map draft on current for SameValue set, missing delete, and clear on an empty map', () => {
      const current = new Map<string, number>([['key', 1]])
      const empty = new Map<string, number>()

      const unchanged = createPatch(current, (draft) => {
        draft.set('key', 1)
        draft.delete('missing')
        return draft
      })

      const unchangedEmpty = createPatch(empty, (draft) => {
        draft.clear()
        return draft
      })

      assert.equal(unchanged, current)
      assert.equal(unchangedEmpty, empty)
    })

    it('keeps a set draft on current for duplicate add, missing delete, and clear on an empty set', () => {
      const current = new Set<number>([1, 2])
      const empty = new Set<number>()

      const unchanged = createPatch(current, (draft) => {
        draft.add(2)
        draft.delete(3)
        return draft
      })

      const unchangedEmpty = createPatch(empty, (draft) => {
        draft.clear()
        return draft
      })

      assert.equal(unchanged, current)
      assert.equal(unchangedEmpty, empty)
    })

    it('keeps clone-on-read specials unchanged on pure reads at the finalized value boundary', () => {
      const date = new Date('2024-01-01T00:00:00.000Z')
      const buffer = new Uint8Array([1, 2, 3, 4]).buffer
      const current = {
        date,
        typed: new Uint8Array(buffer),
        view: new DataView(buffer),
      }

      const result = createPatch(current, (draft) => {
        assert.equal(draft.date.getUTCFullYear(), 2024)
        assert.deepEqual(Array.from(draft.typed), [1, 2, 3, 4])
        assert.equal(draft.view.getUint8(0), 1)
        return draft
      })

      // Reading specials creates clone-on-read tracking, so the wrapper object may be rebuilt.
      // The public contract we need to preserve is that unchanged special clones collapse back to
      // the original current-backed special values at the finalized boundary.
      assert.equal(result.date, date)
      assert.equal(result.typed, current.typed)
      assert.equal(result.view, current.view)
    })
  })

  describe('first real mutation is sticky and there is no restoration', () => {
    it('treats plain-object add then delete of the same property as a sticky mutation', () => {
      const current = { nested: { value: 1 } }

      const result = createPatch(current, (draft) => {
        ;(draft.nested as { extra?: boolean } & typeof draft.nested).extra = true
        delete (draft.nested as { extra?: boolean } & typeof draft.nested).extra
        return draft
      })

      assert.notEqual(result, current)
      assert.notEqual(result.nested, current.nested)
      assert.deepEqual(result, { nested: { value: 1 } })
    })

    it('treats array mutate-then-mutate-back as a sticky mutation', () => {
      const current = [1, 2, 3]

      const result = createPatch(current, (draft) => {
        draft[1] = 9
        draft[1] = 2
        return draft
      })

      assert.notEqual(result, current)
      assert.deepEqual(result, [1, 2, 3])
    })

    it('treats map set-then-set-back as a sticky mutation', () => {
      const current = new Map<string, number>([['key', 1]])

      const result = createPatch(current, (draft) => {
        draft.set('key', 9)
        draft.set('key', 1)
        return draft
      })

      assert.notEqual(result, current)
      assert.deepEqual(Array.from(result.entries()), [['key', 1]])
    })

    it('treats set delete plus add of the same value as ordinary sticky mutation', () => {
      const current = new Set([1, 2, 3])

      const result = createPatch(current, (draft) => {
        draft.delete(1)
        draft.add(1)
        return draft
      })

      assert.notEqual(result, current)
      assert.deepEqual(Array.from(result.values()), [2, 3, 1])
      assert.deepEqual(Array.from(current.values()), [1, 2, 3])
    })
  })

  describe('SameValue parent writes do not discard child-draft mutations', () => {
    it('keeps a child object mutation sticky when the parent property receives the original reference back', () => {
      const child = { count: 1 }
      const current = { child }

      const result = createPatch(current, (draft) => {
        const childDraft = draft.child
        childDraft.count = 2
        draft.child = child
        return draft
      })

      assert.notEqual(result, current)
      assert.notEqual(result.child, child)
      assert.equal(result.child.count, 2)
      assert.equal(current.child.count, 1)
    })

    it('keeps shared-image coherence when a map entry receives the original shared reference back', () => {
      const shared = { count: 1 }
      const current = {
        map: new Map<string, { count: number }>([['key', shared]]),
        shared,
      }

      const result = createPatch(current, (draft) => {
        draft.shared.count = 2
        void draft.map
        draft.map.set('key', shared)
        return draft
      })

      assert.equal(result.shared, result.map.get('key'))
      assert.equal(result.shared.count, 2)
      assert.notEqual(result.shared, shared)
    })

    it('keeps shared-image coherence when an array element receives the original shared reference back', () => {
      const shared = { count: 1 }
      const current = {
        array: [shared, shared],
        shared,
      }

      const result = createPatch(current, (draft) => {
        draft.shared.count = 2
        draft.array[1] = shared
        return draft
      })

      assert.equal(result.array[0], result.array[1])
      assert.equal(result.array[0], result.shared)
      assert.equal(result.array[0].count, 2)
      assert.notEqual(result.array[0], shared)
    })
  })

  describe('unmodified returned draft handles still materialize changed descendants', () => {
    it('materializes a plain-object handle whose shared descendant changed elsewhere', () => {
      const shared = { count: 1 }
      const current = {
        left: { shared },
        right: { shared },
      }

      const result = createPatch(current, (draft) => {
        draft.left.shared.count = 2
        return draft.right
      })

      assert.notEqual(result, current.right)
      assert.notEqual(result.shared, shared)
      assert.equal(result.shared.count, 2)
    })

    it('materializes an array handle whose shared element changed elsewhere', () => {
      const shared = { count: 1 }
      const current = {
        left: { shared },
        right: [shared],
      }

      const result = createPatch(current, (draft) => {
        draft.left.shared.count = 2
        return draft.right
      })

      assert.notEqual(result, current.right)
      assert.notEqual(result[0], shared)
      assert.equal(result[0].count, 2)
    })

    it('materializes a map handle whose shared value changed elsewhere', () => {
      const shared = { count: 1 }
      const current = {
        left: { shared },
        right: new Map<string, { count: number }>([['key', shared]]),
      }

      const result = createPatch(current, (draft) => {
        draft.left.shared.count = 2
        return draft.right
      })

      assert.notEqual(result, current.right)
      assert.notEqual(result.get('key'), shared)
      assert.equal(result.get('key')!.count, 2)
    })

    it('materializes a set handle whose shared value changed elsewhere', () => {
      const shared = { count: 1 }
      const current = {
        left: { shared },
        right: new Set([shared]),
      }

      const result = createPatch(current, (draft) => {
        draft.left.shared.count = 2
        return draft.right
      })

      const entry = firstSetEntry(result)
      assert.notEqual(result, current.right)
      assert.notEqual(entry, shared)
      assert.equal(entry.count, 2)
    })

    it('materializes a plain-object handle that contains a clone-on-read Date changed elsewhere', () => {
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
  })

  describe('returned unmodified nested collection handles unwrap instead of leaking wrappers', () => {
    it('unwraps an unmodified nested map handle back to the base map', () => {
      const current = {
        map: new Map<string, number>([['key', 1]]),
      }

      const result = createPatch(current, (draft) => {
        assert.equal(draft.map.get('key'), 1)
        return draft.map
      })

      assert.equal(result, current.map)
      assert.equal(result instanceof Map, true)
    })

    it('unwraps an unmodified nested set handle back to the base set', () => {
      const current = {
        set: new Set<number>([1, 2, 3]),
      }

      const result = createPatch(current, (draft) => {
        assert.equal(draft.set.has(2), true)
        return draft.set
      })

      assert.equal(result, current.set)
      assert.equal(result instanceof Set, true)
    })
  })

  describe('root return semantics remain intact', () => {
    it('still lets `return current` bypass all draft finalization', () => {
      const current = { nested: { count: 1 } }

      const result = createPatch(current, (draft) => {
        draft.nested.count = 2
        return current
      })

      assert.equal(result, current)
      assert.equal(result.nested.count, 1)
    })

    it('still lets an ordinary replacement root win while finalizing nested draft handles inside it', () => {
      const current = {
        item: { count: 1 },
        untouched: { keep: true },
      }

      const result = createPatch(current, (draft) => {
        draft.item.count = 2

        return {
          label: 'replacement',
          wrapped: draft.item,
        }
      })

      assert.deepEqual(result, {
        label: 'replacement',
        wrapped: { count: 2 },
      })
      assert.notEqual(result.wrapped, current.item)
      assert.deepEqual(current, {
        item: { count: 1 },
        untouched: { keep: true },
      })
    })
  })

  describe('clone-on-read binary and view coherence remains intact', () => {
    it('keeps one coherent next-side buffer across ArrayBuffer, DataView, and typed-array paths', () => {
      const buffer = new Uint8Array([1, 2, 3, 4]).buffer
      const current = {
        typed: new Uint8Array(buffer),
        view: new DataView(buffer),
      }

      const result = createPatch(current, (draft) => {
        draft.view.setUint8(1, 9)

        return {
          buffer: draft.view.buffer,
          left: new Uint8Array(draft.view.buffer, 0, 2),
          nested: {
            mirror: draft.view.buffer,
            right: new DataView(draft.view.buffer, 2, 2),
          },
        }
      }) as {
        buffer: ArrayBuffer
        left: Uint8Array
        nested: {
          mirror: ArrayBuffer
          right: DataView
        }
      }

      assert.equal(result.buffer, result.left.buffer)
      assert.equal(result.buffer, result.nested.mirror)
      assert.equal(result.buffer, result.nested.right.buffer)
      assert.deepEqual(bytesOf(result.buffer), [1, 9, 3, 4])
      assert.deepEqual(Array.from(result.left), [1, 9])
      assert.deepEqual(
        Array.from(
          new Uint8Array(
            result.nested.right.buffer,
            result.nested.right.byteOffset,
            result.nested.right.byteLength,
          ),
        ),
        [3, 4],
      )
    })
  })

  describe('publication still differs intentionally from createPatch on revert-style writes', () => {
    it('lets createPatch diverge while patch may still publish onto the live current graph', () => {
      const current = {
        nested: { count: 0 },
      }

      const next = createPatch(current, (draft) => {
        draft.nested.count = 1
        draft.nested.count = 0
        return draft
      })

      const published = patch(current, (draft) => {
        draft.nested.count = 1
        draft.nested.count = 0
        return draft
      })

      assert.notEqual(next, current)
      assert.notEqual(next.nested, current.nested)
      assert.deepEqual(next, { nested: { count: 0 } })

      assert.equal(published, current)
      assert.equal(published.nested, current.nested)
      assert.deepEqual(published, { nested: { count: 0 } })
    })
  })

  describe('non-regression for draft-originating map keys', () => {
    it('keeps a draft-originating map key finalized coherently after mutate-then-mutate-back', () => {
      const key = { label: 'key' }
      const current = {
        key,
        map: new Map<object, number>([[key, 1]]),
      }

      const result = createPatch(current, (draft) => {
        draft.key.label = 'updated'
        draft.key.label = 'key'
        return draft.map
      })

      const [resultKey] = firstMapEntry(result)
      assert.notEqual(result, current.map)
      assert.notEqual(resultKey, key)
      assert.equal((resultKey as { label: string }).label, 'key')
      assert.equal(result.get(resultKey), 1)
      assert.equal(current.key.label, 'key')
    })
  })
})
