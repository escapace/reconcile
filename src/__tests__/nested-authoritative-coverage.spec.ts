import { assert, describe, it } from 'vitest'

import { createPatch } from '../patch'

const firstSetEntry = <T>(value: Set<T>): T => value.values().next().value!
const firstMapEntry = <K, V>(value: Map<K, V>): readonly [K, V] => value.entries().next().value!
const bytesOf = (value: ArrayBufferLike): number[] => Array.from(new Uint8Array(value))

describe('nested authoritative finalization coverage', () => {
  describe('nested returned draft roots propagate externally changed shared objects', () => {
    it('plain-object root finalizes a shared descendant changed elsewhere', () => {
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
      assert.equal(current.right.shared.count, 1)
    })

    it('array root finalizes a shared element changed elsewhere', () => {
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
      assert.equal(current.right[0].count, 1)
    })

    it('map root finalizes a shared value changed elsewhere', () => {
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
      assert.equal(current.right.get('key')!.count, 1)
    })

    it('set root finalizes a shared value changed elsewhere', () => {
      const shared = { count: 1 }
      const current = {
        left: { shared },
        right: new Set([{ count: 0 }, shared]),
      }

      const result = createPatch(current, (draft) => {
        draft.left.shared.count = 2
        return draft.right
      })

      const entries = Array.from(result.values())
      const finalizedShared = entries[1]

      assert.notEqual(result, current.right)
      assert.notEqual(finalizedShared, shared)
      assert.equal(finalizedShared.count, 2)
      assert.equal(Array.from(current.right.values())[1].count, 1)
    })
  })

  describe('ordinary returned roots finalize nested draft handles coherently', () => {
    it('plain-object handle finalizes when wrapped by an ordinary returned object', () => {
      const shared = { count: 1 }
      const current = {
        left: { shared },
        right: { shared },
      }

      const result = createPatch(current, (draft) => {
        draft.left.shared.count = 2
        return { wrapped: draft.right }
      })

      assert.notEqual(result.wrapped, current.right)
      assert.notEqual(result.wrapped.shared, shared)
      assert.equal(result.wrapped.shared.count, 2)
    })

    it('array handle finalizes when wrapped by an ordinary returned object', () => {
      const shared = { count: 1 }
      const current = {
        left: { shared },
        right: [shared],
      }

      const result = createPatch(current, (draft) => {
        draft.left.shared.count = 2
        return { wrapped: draft.right }
      })

      assert.notEqual(result.wrapped, current.right)
      assert.notEqual(result.wrapped[0], shared)
      assert.equal(result.wrapped[0].count, 2)
    })

    it('map handle finalizes when wrapped by an ordinary returned object', () => {
      const shared = { count: 1 }
      const current = {
        left: { shared },
        right: new Map<string, { count: number }>([['key', shared]]),
      }

      const result = createPatch(current, (draft) => {
        draft.left.shared.count = 2
        return { wrapped: draft.right }
      })

      assert.notEqual(result.wrapped, current.right)
      assert.notEqual(result.wrapped.get('key'), shared)
      assert.equal(result.wrapped.get('key')!.count, 2)
    })

    it('set handle finalizes when wrapped by an ordinary returned object', () => {
      const shared = { count: 1 }
      const current = {
        left: { shared },
        right: new Set([shared]),
      }

      const result = createPatch(current, (draft) => {
        draft.left.shared.count = 2
        return { wrapped: draft.right }
      })

      const entry = firstSetEntry(result.wrapped)
      assert.notEqual(result.wrapped, current.right)
      assert.notEqual(entry, shared)
      assert.equal(entry.count, 2)
    })
  })

  describe('clone-on-read specials propagate through nested returned roots', () => {
    it('plain-object root finalizes a Date changed elsewhere', () => {
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

    it('array root finalizes an ArrayBuffer changed elsewhere', () => {
      const buffer = new Uint8Array([1, 2, 3]).buffer
      const current = {
        left: buffer,
        right: [buffer],
      }

      const result = createPatch(current, (draft) => {
        new Uint8Array(draft.left)[0] = 9
        return draft.right
      })

      assert.notEqual(result, current.right)
      assert.notEqual(result[0], buffer)
      assert.deepEqual(bytesOf(result[0]), [9, 2, 3])
      assert.deepEqual(bytesOf(current.right[0]), [1, 2, 3])
    })

    it('map root finalizes a DataView changed elsewhere', () => {
      const buffer = new Uint8Array([1, 2, 3, 4]).buffer
      const view = new DataView(buffer)
      const current = {
        left: view,
        right: new Map<string, DataView>([['key', view]]),
      }

      const result = createPatch(current, (draft) => {
        draft.left.setUint8(1, 9)
        return draft.right
      })

      const finalizedView = result.get('key')!
      assert.notEqual(result, current.right)
      assert.notEqual(finalizedView, view)
      assert.deepEqual(
        Array.from(
          new Uint8Array(finalizedView.buffer, finalizedView.byteOffset, finalizedView.byteLength),
        ),
        [1, 9, 3, 4],
      )
      assert.deepEqual(
        Array.from(new Uint8Array(view.buffer, view.byteOffset, view.byteLength)),
        [1, 2, 3, 4],
      )
    })

    it('set root finalizes a typed array changed elsewhere', () => {
      const typed = new Uint16Array([5, 6, 7])
      const current = {
        left: typed,
        right: new Set<Uint16Array>([typed]),
      }

      const result = createPatch(current, (draft) => {
        draft.left[1] = 9
        return draft.right
      })

      const finalizedTyped = firstSetEntry(result)
      assert.notEqual(result, current.right)
      assert.notEqual(finalizedTyped, typed)
      assert.deepEqual(Array.from(finalizedTyped), [5, 9, 7])
      assert.deepEqual(Array.from(typed), [5, 6, 7])
    })
  })

  describe('nested authoritative returns follow the monotonic write model', () => {
    it('plain-object root finalizes a fresh subtree when a shared descendant changed elsewhere', () => {
      const shared = { count: 1 }
      const current = {
        right: { shared },
        shared,
      }

      const result = createPatch(current, (draft) => {
        draft.shared.count = 2
        draft.right.shared = shared // SameValue write: no restoration
        return draft.right
      })

      assert.notEqual(result, current.right)
      assert.notEqual(result.shared, shared)
      assert.equal(result.shared.count, 2)
    })

    it('array root finalizes a fresh subtree when a shared element changed elsewhere', () => {
      const shared = { count: 1 }
      const current = {
        right: [shared],
        shared,
      }

      const result = createPatch(current, (draft) => {
        draft.shared.count = 2
        draft.right[0] = shared // SameValue write: no restoration
        return draft.right
      })

      assert.notEqual(result, current.right)
      assert.notEqual(result[0], shared)
      assert.equal(result[0].count, 2)
    })

    it('map root finalizes a fresh subtree when a shared value changed elsewhere', () => {
      const shared = { count: 1 }
      const current = {
        right: new Map<string, { count: number }>([['key', shared]]),
        shared,
      }

      const result = createPatch(current, (draft) => {
        draft.shared.count = 2
        draft.right.set('key', shared) // SameValue write: no restoration
        return draft.right
      })

      assert.notEqual(result, current.right)
      assert.notEqual(result.get('key'), shared)
      assert.equal(result.get('key')!.count, 2)
    })

    it('set root stays modified after delete plus re-add of the same value', () => {
      const shared = { count: 1 }
      const current = {
        right: new Set([shared]),
        shared,
      }

      const result = createPatch(current, (draft) => {
        draft.right.delete(shared)
        draft.right.add(shared)
        return draft.right
      })

      assert.notEqual(result, current.right)
      const entry = firstSetEntry(result)
      assert.equal(entry, shared)
      assert.equal(entry.count, 1)
    })

    it('set root keeps collection-local membership semantics after delete plus re-add of a shared value changed elsewhere', () => {
      const shared = { count: 1 }
      const current = {
        right: new Set([{ keep: true }, shared]),
        shared,
      }

      const result = createPatch(current, (draft) => {
        draft.shared.count = 2
        draft.right.delete(shared)
        draft.right.add(shared)
        return draft.right
      })

      const entries = Array.from(result.values()) as Array<{ count?: number; keep?: boolean }>
      assert.notEqual(result, current.right)
      assert.deepEqual(entries[0], { keep: true })
      assert.notEqual(entries[1], shared)
      assert.equal(entries[1].count, 2)
      assert.equal(shared.count, 1)
    })
  })

  describe('supported cross-position coherence survives nested authoritative returns', () => {
    it('map roots finalize draft-originating keys coherently with ordinary object paths', () => {
      const key = { id: 'key' }
      const current = {
        key,
        map: new Map<object, number>([[key, 1]]),
      }

      const result = createPatch(current, (draft) => {
        draft.key.id = 'updated'
        return draft.map
      })

      const [resultKey] = firstMapEntry(result)
      assert.notEqual(result, current.map)
      assert.notEqual(resultKey, key)
      assert.equal((resultKey as { id: string }).id, 'updated')
      assert.equal(result.get(resultKey), 1)
    })

    it('set roots finalize shared draft-originating values coherently with ordinary object paths', () => {
      const shared = { count: 1 }
      const current = {
        set: new Set([shared]),
        shared,
      }

      const result = createPatch(current, (draft) => {
        draft.shared.count = 3
        return draft.set
      })

      const entry = firstSetEntry(result)
      assert.notEqual(result, current.set)
      assert.notEqual(entry, shared)
      assert.equal(entry.count, 3)
    })
  })
})
