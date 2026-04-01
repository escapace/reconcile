import { assert, describe, it } from 'vitest'
import { createPatch, patch } from '../patch'
import { snapshot } from '../snapshot'

/**
 * Comprehensive verification suite for finalization coherence semantics.
 *
 * This suite locks in the behavioral guarantees derived from:
 * - Lean `sharedImage` theorem: shared draft-originating values must finalize to the same identity
 * - Lean `movedImage` theorem: moved values must appear at their final locations
 * - Lean `capturedImage` theorem: collection-captured draft values must finalize coherently
 *
 * The tests are organized by semantic guarantee rather than data type, ensuring
 * each guarantee is verified across all supported value kinds.
 */

// Helper functions
const firstSetEntry = <T>(value: Set<T>): T => value.values().next().value!
const firstMapEntry = <K, V>(value: Map<K, V>): readonly [K, V] => value.entries().next().value!
const bytesOf = (value: ArrayBufferLike): number[] => Array.from(new Uint8Array(value))

describe('Finalization Coherence - sharedImage Guarantee', () => {
  describe('Plain Objects: shared references finalize to same identity', () => {
    it('preserves sharing when same object appears in multiple properties', () => {
      const shared = { value: 1 }
      const current = { a: shared, b: shared, c: shared }

      const result = createPatch(current, (draft: typeof current) => {
        draft.a.value = 2
        return draft
      })

      assert.equal(result.a, result.b)
      assert.equal(result.b, result.c)
      assert.equal(result.a.value, 2)
      assert.notEqual(result.a, shared)
    })

    it('preserves sharing across nested object hierarchies', () => {
      const shared = { count: 0 }
      const current = {
        level1: { child: shared },
        level2: { nested: { child: shared } },
      }

      const result = createPatch(current, (draft: typeof current) => {
        draft.level1.child.count = 5
        return draft
      })

      assert.equal(result.level1.child, result.level2.nested.child)
      assert.equal(result.level1.child.count, 5)
    })

    it('preserves sharing when only deep path is touched', () => {
      const shared = { deep: { value: 0 } }
      const current = { x: shared, y: shared }

      const result = createPatch(current, (draft: typeof current) => {
        draft.x.deep.value = 10
        return draft
      })

      assert.equal(result.x, result.y)
      assert.equal(result.x.deep, result.y.deep)
      assert.equal(result.x.deep.value, 10)
    })
  })

  describe('Arrays: shared references finalize to same identity', () => {
    it('preserves sharing when same object appears at multiple indices', () => {
      const shared = { id: 1 }
      const current = [shared, shared, shared]

      const result = createPatch(current, (draft: typeof current) => {
        draft[0].id = 2
        return draft
      })

      assert.equal(result[0], result[1])
      assert.equal(result[1], result[2])
      assert.equal(result[0].id, 2)
    })

    it('preserves sharing in nested arrays', () => {
      const shared = { value: 'a' }
      const current = [[shared], [shared, shared]]

      const result = createPatch(current, (draft: typeof current) => {
        draft[0][0].value = 'b'
        return draft
      })

      assert.equal(result[0][0], result[1][0])
      assert.equal(result[1][0], result[1][1])
      assert.equal(result[0][0].value, 'b')
    })

    it('preserves sharing across array and object containers', () => {
      const shared = { count: 0 }
      const current = {
        array: [shared],
        object: { ref: shared },
      }

      const result = createPatch(current, (draft: typeof current) => {
        draft.array[0].count = 3
        return draft
      })

      assert.equal(result.array[0], result.object.ref)
      assert.equal(result.array[0].count, 3)
    })
  })

  describe('Maps: shared references finalize to same identity', () => {
    it('preserves sharing when same object is a value in multiple map entries', () => {
      const shared = { data: 0 }
      const current = new Map([
        ['a', shared],
        ['b', shared],
      ])

      const result = createPatch(current, (draft: typeof current) => {
        draft.get('a')!.data = 7
        return draft
      })

      assert.equal(result.get('a'), result.get('b'))
      assert.equal(result.get('a')!.data, 7)
    })

    it('preserves sharing between map values and plain object properties', () => {
      const shared = { value: 1 }
      const current = {
        map: new Map([['key', shared]]),
        ref: shared,
      }

      const result = createPatch(current, (draft: typeof current) => {
        draft.ref.value = 2
        return draft
      })

      assert.equal(result.ref, result.map.get('key'))
      assert.equal(result.ref.value, 2)
    })

    it('preserves sharing for object-valued map keys', () => {
      const sharedKey = { id: 'key' }
      const current = {
        key: sharedKey,
        map: new Map<object, number>([[sharedKey, 1]]),
      }

      const result = createPatch(current, (draft: typeof current) => {
        draft.key.id = 'updated'
        return draft
      })

      const [mapKey] = firstMapEntry(result.map)
      assert.equal(mapKey, result.key)
      assert.equal((mapKey as { id: string }).id, 'updated')
    })
  })

  describe('Sets: shared references finalize to same identity', () => {
    it('preserves sharing between set element and plain object property', () => {
      const shared = { count: 0 }
      const current = {
        ref: shared,
        set: new Set([shared]),
      }

      const result = createPatch(current, (draft: typeof current) => {
        draft.ref.count = 4
        return draft
      })

      assert.equal(firstSetEntry(result.set), result.ref)
      assert.equal(result.ref.count, 4)
    })

    it('preserves sharing between set element and array element', () => {
      const shared = { value: 'x' }
      const current = {
        array: [shared],
        set: new Set([shared]),
      }

      const result = createPatch(current, (draft: typeof current) => {
        draft.array[0].value = 'y'
        return draft
      })

      assert.equal(firstSetEntry(result.set), result.array[0])
      assert.equal(result.array[0].value, 'y')
    })
  })

  describe('Cross-container sharing', () => {
    it('preserves sharing when same object appears in object, array, map, and set', () => {
      const shared = { id: 0 }
      const current = {
        array: [shared],
        map: new Map([['k', shared]]),
        obj: shared,
        set: new Set([shared]),
      }

      const result = createPatch(current, (draft: typeof current) => {
        draft.obj.id = 99
        return draft
      })

      assert.equal(result.obj, result.array[0])
      assert.equal(result.obj, result.map.get('k'))
      assert.equal(result.obj, firstSetEntry(result.set))
      assert.equal(result.obj.id, 99)
    })

    it('preserves sharing across deeply nested mixed containers', () => {
      const shared = { deep: true }
      const current = {
        level1: {
          array: [{ nested: shared }],
          map: new Map([['key', { wrapped: shared }]]),
        },
      }

      const result = createPatch(current, (draft: typeof current) => {
        draft.level1.array[0].nested.deep = false
        return draft
      })

      assert.equal(result.level1.array[0].nested, result.level1.map.get('key')!.wrapped)
      assert.equal(result.level1.array[0].nested.deep, false)
    })
  })
})

describe('Finalization Coherence - SameValue Writes and Root Return', () => {
  describe('Plain Objects: SameValue writes remain no-ops and preserve sharing', () => {
    it('treats writing the original reference back at a sibling path as a no-op', () => {
      // Under the monotonic write model, `draft.b.ref = shared` is a SameValue write against
      // the existing present slot, so the `b` draft stays unmodified. The shared object was
      // changed elsewhere, so shared-image coherence still resolves `b.ref` to the same
      // finalized identity as `a.ref`.
      const shared = { value: 1 }
      const current = { a: { ref: shared }, b: { ref: shared } }

      const result = createPatch(current, (draft: typeof current) => {
        draft.a.ref.value = 2
        void draft.b
        draft.b.ref = shared // SameValue write: no-op
        return draft
      })

      assert.equal(result.a.ref, result.b.ref)
      assert.equal(result.a.ref.value, 2)
      assert.notEqual(result.a.ref, shared)
    })

    it('honors an explicit root-level return of current and ignores all draft mutations', () => {
      // Returning `current` from the recipe is still a first-class escape hatch. It bypasses
      // draft finalization entirely and is the only path that discards monotonic draft changes.
      const current = { nested: { count: 1 } }

      const result = createPatch(current, (draft: typeof current) => {
        draft.nested.count = 99
        return current
      })

      assert.equal(result, current)
      assert.equal(result.nested.count, 1)
    })
  })

  describe('Arrays: SameValue writes remain no-ops and preserve sharing', () => {
    it('treats writing the original element back as a no-op', () => {
      // `draft[1] = shared` is a SameValue write against the existing present slot, so the
      // array draft stays unmodified. The finalized array still points to the same finalized
      // image as the other, mutated path.
      const shared = { id: 1 }
      const current = [shared, shared]

      const result = createPatch(current, (draft: typeof current) => {
        draft[0].id = 2
        draft[1] = shared // SameValue write: no-op
        return draft
      })

      assert.equal(result[0], result[1])
      assert.equal(result[0].id, 2)
      assert.notEqual(result[0], shared)
    })
  })

  describe('Maps: SameValue set calls remain no-ops and preserve sharing', () => {
    it('treats setting an entry to its current value as a no-op', () => {
      // `draft.map.set('b', shared)` is a SameValue set against the existing entry, so the map
      // draft stays unmodified. The finalized map value at `b` is the same finalized image as
      // the other paths that reach `shared`.
      const shared = { data: 1 }
      const current = {
        map: new Map([
          ['a', shared],
          ['b', shared],
        ]),
        ref: shared,
      }

      const result = createPatch(current, (draft: typeof current) => {
        draft.ref.data = 2
        draft.map.set('b', shared) // SameValue set: no-op
        return draft
      })

      assert.equal(result.ref, result.map.get('b'))
      assert.equal(result.map.get('a'), result.map.get('b'))
      assert.equal(result.map.get('b')!.data, 2)
    })
  })

  describe('Shared-image coherence through publication', () => {
    it('reconcile publishes one coherent shared value for a monotonic mutation', () => {
      // All paths reach the same finalized image, and publication through reconcile updates
      // the shared reference in place.
      const shared = { count: 0 }
      const current = { a: { ref: shared }, c: { ref: shared } }

      const result = patch(current, (draft: typeof current) => {
        draft.a.ref.count = 5
        void draft.c
        draft.c.ref = shared // SameValue write: no-op
        return draft
      })

      assert.equal(result.a.ref, result.c.ref)
      assert.equal(result.a.ref, shared)
      assert.equal(shared.count, 5)
    })

    it('publishes one coherent shared value for a shared object aliased at two sibling paths', () => {
      // All paths resolve to the same finalized image, and publication through reconcile
      // updates the shared reference in place while keeping sibling identities coherent.
      const shared = { count: 0 }
      const current = { a: shared, b: shared }

      const result = patch(current, (draft: typeof current) => {
        draft.a.count = 5
        void draft.b
        draft.b = shared // SameValue write: no-op
        return draft
      })

      assert.equal(result.a, result.b)
      assert.equal(result.a, shared)
      assert.equal(shared.count, 5)
    })
  })
})

describe('Finalization Coherence - movedImage Guarantee', () => {
  describe('Plain Objects: moved values appear at final locations', () => {
    it('moves a value from one property to another', () => {
      const current: { source?: { value: number }; target?: { value: number } } = {
        source: { value: 1 },
      }

      const result = createPatch(current, (draft: typeof current) => {
        const moved = draft.source!
        delete draft.source
        draft.target = moved
        moved.value = 2
        return draft
      })

      assert.equal('source' in result, false)
      assert.deepEqual(result.target, { value: 2 })
    })

    it('moves a value while maintaining sharing with existing references', () => {
      const shared = { count: 0 }
      const current: {
        existing: { count: number }
        source?: { count: number }
        target?: { count: number }
      } = {
        existing: shared,
        source: shared,
      }

      const result = createPatch(current, (draft: typeof current) => {
        const moved = draft.source!
        delete draft.source
        draft.target = moved
        moved.count = 10
        return draft
      })

      assert.equal('source' in result, false)
      assert.equal(result.existing, result.target)
      assert.equal(result.existing.count, 10)
    })
  })

  describe('Arrays: moved values appear at final positions', () => {
    it('moves a value between array positions', () => {
      const current = [{ id: 1 }, { id: 2 }, { id: 3 }]

      const result = createPatch(current, (draft: typeof current) => {
        const moved = draft[0]
        draft.splice(0, 1)
        draft.push(moved)
        moved.id = 99
        return draft
      })

      assert.deepEqual(result, [{ id: 2 }, { id: 3 }, { id: 99 }])
    })

    it('moves a value from object to array', () => {
      const current: {
        array: Array<{ value: number }>
        source?: { value: number }
      } = {
        array: [],
        source: { value: 1 },
      }

      const result = createPatch(current, (draft: typeof current) => {
        const moved = draft.source!
        delete draft.source
        draft.array.push(moved)
        moved.value = 5
        return draft
      })

      assert.equal('source' in result, false)
      assert.deepEqual(result.array, [{ value: 5 }])
    })
  })

  describe('Collections: moved values appear in final collections', () => {
    it('moves a value from object to map', () => {
      const current: {
        map: Map<string, { data: number }>
        source?: { data: number }
      } = {
        map: new Map(),
        source: { data: 1 },
      }

      const result = createPatch(current, (draft: typeof current) => {
        const moved = draft.source!
        delete draft.source
        draft.map.set('moved', moved)
        moved.data = 7
        return draft
      })

      assert.equal('source' in result, false)
      assert.deepEqual(result.map.get('moved'), { data: 7 })
    })

    it('moves a value from array to set', () => {
      const current: {
        array: Array<{ id: number }>
        set: Set<{ id: number }>
      } = {
        array: [{ id: 1 }],
        set: new Set(),
      }

      const result = createPatch(current, (draft: typeof current) => {
        const moved = draft.array[0]
        draft.array.splice(0, 1)
        draft.set.add(moved)
        moved.id = 8
        return draft
      })

      assert.deepEqual(result.array, [])
      assert.deepEqual(firstSetEntry(result.set), { id: 8 })
    })
  })
})

describe('Finalization Coherence - capturedImage Guarantee', () => {
  describe('Draft values captured in arrays', () => {
    it('finalizes draft captured by push', () => {
      const current = {
        item: { count: 0 },
        list: [] as Array<{ count: number }>,
      }

      const result = createPatch(current, (draft: typeof current) => {
        draft.item.count = 1
        draft.list.push(draft.item)
        return draft
      })

      assert.equal(result.list[0], result.item)
      assert.equal(result.item.count, 1)
    })

    it('finalizes draft captured by splice insertion', () => {
      const current = {
        item: { value: 'a' },
        list: [{ value: 'x' }],
      }

      const result = createPatch(current, (draft: typeof current) => {
        draft.item.value = 'b'
        draft.list.splice(0, 0, draft.item)
        return draft
      })

      assert.equal(result.list[0], result.item)
      assert.equal(result.item.value, 'b')
    })

    it('finalizes draft captured by index assignment', () => {
      const current = {
        item: { id: 1 },
        list: [null as { id: number } | null],
      }

      const result = createPatch(current, (draft: typeof current) => {
        draft.item.id = 2
        draft.list[0] = draft.item
        return draft
      })

      assert.equal(result.list[0], result.item)
      assert.equal(result.item.id, 2)
    })
  })

  describe('Draft values captured in maps', () => {
    it('finalizes draft captured as map value', () => {
      const current = {
        item: { data: 0 },
        map: new Map<string, { data: number }>(),
      }

      const result = createPatch(current, (draft: typeof current) => {
        draft.item.data = 5
        draft.map.set('captured', draft.item)
        return draft
      })

      assert.equal(result.map.get('captured'), result.item)
      assert.equal(result.item.data, 5)
    })

    it('finalizes draft captured as map key', () => {
      const current = {
        key: { id: 'original' },
        map: new Map<object, number>(),
      }

      const result = createPatch(current, (draft: typeof current) => {
        draft.key.id = 'updated'
        draft.map.set(draft.key, 1)
        return draft
      })

      const [capturedKey] = firstMapEntry(result.map)
      assert.equal(capturedKey, result.key)
      assert.equal((capturedKey as { id: string }).id, 'updated')
    })
  })

  describe('Draft values captured in sets', () => {
    it('finalizes draft captured by add', () => {
      const current = {
        item: { value: 0 },
        set: new Set<{ value: number }>(),
      }

      const result = createPatch(current, (draft: typeof current) => {
        draft.item.value = 3
        draft.set.add(draft.item)
        return draft
      })

      assert.equal(firstSetEntry(result.set), result.item)
      assert.equal(result.item.value, 3)
    })
  })

  describe('Draft values captured in multiple locations', () => {
    it('finalizes draft captured in array, map, and set simultaneously', () => {
      const current = {
        array: [] as Array<{ id: number }>,
        item: { id: 0 },
        map: new Map<string, { id: number }>(),
        set: new Set<{ id: number }>(),
      }

      const result = createPatch(current, (draft: typeof current) => {
        draft.item.id = 42
        draft.array.push(draft.item)
        draft.map.set('key', draft.item)
        draft.set.add(draft.item)
        return draft
      })

      assert.equal(result.array[0], result.item)
      assert.equal(result.map.get('key'), result.item)
      assert.equal(firstSetEntry(result.set), result.item)
      assert.equal(result.item.id, 42)
    })
  })
})

describe('Finalization Coherence - Cycles and Self-References', () => {
  describe('Self-referential structures', () => {
    it('preserves self-reference after mutation', () => {
      interface SelfReference {
        value: number
        self?: SelfReference
      }
      const current: SelfReference = { value: 0 }
      current.self = current

      const result = createPatch(current, (draft: SelfReference) => {
        draft.value = 5
        return draft
      })

      assert.equal(result.self, result)
      assert.equal(result.value, 5)
      assert.notEqual(result, current)
    })

    it('preserves self-reference in array', () => {
      type SelfReferenceArray = Array<number | SelfReferenceArray>
      const current: SelfReferenceArray = [1, 2]
      current.push(current)

      const result = createPatch(current, (draft: SelfReferenceArray) => {
        draft[0] = 10
        return draft
      })

      assert.equal(result[2], result)
      assert.equal(result[0], 10)
    })
  })

  describe('Mutual references', () => {
    it('preserves mutual references between objects', () => {
      interface NodeA {
        value: number
        b?: NodeB
      }
      interface NodeB {
        value: string
        a?: NodeA
      }
      const a: NodeA = { value: 1 }
      const b: NodeB = { value: 'x' }
      a.b = b
      b.a = a

      const current = { a, b }

      const result = createPatch(current, (draft: typeof current) => {
        draft.a.value = 2
        draft.b.value = 'y'
        return draft
      })

      assert.equal(result.a.b, result.b)
      assert.equal(result.b.a, result.a)
      assert.equal(result.a.value, 2)
      assert.equal(result.b.value, 'y')
    })
  })

  describe('Cycles with sharing', () => {
    it('preserves shared reference in cyclic structure', () => {
      interface Node {
        value: number
        next?: Node
      }
      const shared: Node = { value: 0 }
      const current: { head: Node; shared: Node } = {
        head: { next: shared, value: 1 },
        shared,
      }
      shared.next = current.head // Create cycle: head -> shared -> head

      const result = createPatch(current, (draft: typeof current) => {
        draft.shared.value = 99
        return draft
      })

      assert.equal(result.head.next, result.shared)
      assert.equal(result.shared.next, result.head)
      assert.equal(result.shared.value, 99)
    })
  })
})

describe('Finalization Coherence - Special Values', () => {
  describe('Date: shared Date references', () => {
    it('preserves sharing for Date objects', () => {
      const sharedDate = new Date('2024-01-01')
      const current = { a: sharedDate, b: sharedDate }

      const result = createPatch(current, (draft: typeof current) => {
        draft.a.setFullYear(2025)
        return draft
      })

      assert.equal(result.a, result.b)
      assert.equal(result.a.getFullYear(), 2025)
    })

    it('preserves sharing for Date in mixed containers', () => {
      const sharedDate = new Date('2024-06-15')
      const current = {
        array: [sharedDate],
        date: sharedDate,
        map: new Map([['d', sharedDate]]),
      }

      const result = createPatch(current, (draft: typeof current) => {
        draft.date.setMonth(11)
        return draft
      })

      assert.equal(result.date, result.array[0])
      assert.equal(result.date, result.map.get('d'))
      assert.equal(result.date.getMonth(), 11)
    })
  })

  describe('ArrayBuffer: shared buffer references', () => {
    it('preserves sharing for ArrayBuffer', () => {
      const sharedBuffer = new Uint8Array([1, 2, 3]).buffer
      const current = { a: sharedBuffer, b: sharedBuffer }

      const result = createPatch(current, (draft: typeof current) => {
        new Uint8Array(draft.a)[0] = 9
        return draft
      })

      assert.equal(result.a, result.b)
      assert.deepEqual(bytesOf(result.a), [9, 2, 3])
    })
  })

  describe('TypedArray: shared typed array references', () => {
    it('preserves sharing for typed arrays', () => {
      const sharedTyped = new Uint8Array([1, 2, 3])
      const current = { x: sharedTyped, y: sharedTyped }

      const result = createPatch(current, (draft: typeof current) => {
        draft.x[1] = 9
        return draft
      })

      assert.equal(result.x, result.y)
      assert.deepEqual(Array.from(result.x), [1, 9, 3])
    })

    it('preserves buffer aliasing across typed arrays', () => {
      const buffer = new Uint8Array([1, 2, 3, 4]).buffer
      const current = {
        left: new Uint8Array(buffer, 0, 2),
        right: new Uint8Array(buffer, 2, 2),
      }

      const result = createPatch(current, (draft: typeof current) => {
        draft.left[0] = 9
        return draft
      })

      assert.equal(result.left.buffer, result.right.buffer)
      assert.deepEqual(bytesOf(result.left.buffer), [9, 2, 3, 4])
    })
  })

  describe('DataView: shared DataView references', () => {
    it('preserves sharing for DataView', () => {
      const buffer = new Uint8Array([1, 2, 3, 4]).buffer
      const sharedView = new DataView(buffer)
      const current = { a: sharedView, b: sharedView }

      const result = createPatch(current, (draft: typeof current) => {
        draft.a.setUint8(0, 9)
        return draft
      })

      assert.equal(result.a, result.b)
      assert.equal(result.a.getUint8(0), 9)
    })
  })
})

describe('Finalization Coherence - Structural Preservation', () => {
  describe('Plain object key order', () => {
    it('preserves key order after mutation', () => {
      const current = { alpha: 1, bravo: 2, charlie: 3 }

      const result = createPatch(current, (draft: typeof current) => {
        draft.bravo = 20
        return draft
      })

      assert.deepEqual(Object.keys(result), ['alpha', 'bravo', 'charlie'])
    })

    it('preserves key order after delete and recreate', () => {
      const current: { a: number; b: number; c?: number } = { a: 1, b: 2, c: 3 }

      const result = createPatch(current, (draft: typeof current) => {
        delete draft.c
        draft.c = 30
        return draft
      })

      // c moves to end after delete + recreate
      assert.deepEqual(Object.keys(result), ['a', 'b', 'c'])
    })
  })

  describe('Array holes vs undefined', () => {
    it('distinguishes hole from present undefined', () => {
      const current = [1, 2, 3] as Array<number | undefined>

      const result = createPatch(current, (draft: typeof current) => {
        Reflect.deleteProperty(draft, 1) // Create hole
        draft[2] = undefined // Present undefined
        return draft
      })

      assert.equal(1 in result, false) // Hole
      assert.equal(2 in result, true) // Present
      assert.equal(result[2], undefined)
    })
  })

  describe('Map entry order', () => {
    it('preserves map entry order after value mutation', () => {
      const current = new Map([
        ['a', 1],
        ['b', 2],
        ['c', 3],
      ])

      const result = createPatch(current, (draft: typeof current) => {
        draft.set('b', 20)
        return draft
      })

      assert.deepEqual(Array.from(result.keys()), ['a', 'b', 'c'])
    })

    it('moves entry to end on delete + set', () => {
      const current = new Map([
        ['a', 1],
        ['b', 2],
        ['c', 3],
      ])

      const result = createPatch(current, (draft: typeof current) => {
        draft.delete('b')
        draft.set('b', 20)
        return draft
      })

      assert.deepEqual(Array.from(result.keys()), ['a', 'c', 'b'])
    })
  })

  describe('Set value order', () => {
    it('preserves set order after add/delete', () => {
      const current = new Set([1, 2, 3])

      const result = createPatch(current, (draft: typeof current) => {
        draft.delete(2)
        draft.add(4)
        return draft
      })

      assert.deepEqual(Array.from(result), [1, 3, 4])
    })

    it('moves element to end on delete + re-add', () => {
      const current = new Set([1, 2, 3])

      const result = createPatch(current, (draft: typeof current) => {
        draft.delete(1)
        draft.add(1)
        return draft
      })

      assert.deepEqual(Array.from(result), [2, 3, 1])
    })
  })
})

describe('Finalization Coherence - Detachment Guarantees', () => {
  describe('snapshot(createPatch(...)) produces detached result', () => {
    it('detaches untouched shared references', () => {
      const shared = { value: 1 }
      const current = { a: shared, b: shared }

      const result = snapshot(
        createPatch(current, (draft: typeof current) => {
          draft.a.value = 2
          return draft
        }),
      ) as typeof current

      // Detached, so not equal to original
      assert.notEqual(result.a, shared)
      assert.notEqual(result.b, shared)
      // But sharing is preserved within result
      assert.equal(result.a, result.b)
      assert.equal(result.a.value, 2)
    })

    it('detaches the finalized shared value coherently after a SameValue sibling write', () => {
      // Under the monotonic write model, `draft.y = shared` is a SameValue write and never
      // marks the draft modified. The two sibling paths resolve to the same finalized image,
      // and `snapshot(...)` detaches that single image cleanly.
      const shared = { count: 1 }
      const current = { x: shared, y: shared }

      const result = snapshot(
        createPatch(current, (draft: typeof current) => {
          draft.x.count = 2
          void draft.y
          draft.y = shared // SameValue write: no-op
          return draft
        }),
      ) as typeof current

      assert.notEqual(result.x, shared)
      assert.notEqual(result.y, shared)
      // Both sibling paths share one finalized image, and the change is reflected coherently.
      assert.equal(result.x, result.y)
      assert.equal(result.x.count, 2)
    })
  })
})

describe('Finalization Coherence - Edge Cases', () => {
  describe('Empty containers', () => {
    it('handles empty array with sharing', () => {
      const empty: never[] = []
      const current = { a: empty, b: empty }

      const result = createPatch(current, (draft: typeof current) => draft)

      assert.equal(result.a, result.b)
      assert.equal(result.a, empty)
    })

    it('handles empty map with sharing', () => {
      const empty = new Map<string, number>()
      const current = { a: empty, b: empty }

      const result = createPatch(current, (draft: typeof current) => draft)

      assert.equal(result.a, result.b)
      assert.equal(result.a, empty)
    })

    it('handles empty set with sharing', () => {
      const empty = new Set<number>()
      const current = { a: empty, b: empty }

      const result = createPatch(current, (draft: typeof current) => draft)

      assert.equal(result.a, result.b)
      assert.equal(result.a, empty)
    })
  })

  describe('Deeply nested shared references', () => {
    it('preserves sharing at arbitrary depth', () => {
      const shared = { leaf: true }
      const current = {
        path1: { l1: { l2: { l3: shared } } },
        path2: { a: { b: { c: { d: shared } } } },
      }

      const result = createPatch(current, (draft: typeof current) => {
        draft.path1.l1.l2.l3.leaf = false
        return draft
      })

      assert.equal(result.path1.l1.l2.l3, result.path2.a.b.c.d)
      assert.equal(result.path1.l1.l2.l3.leaf, false)
    })
  })

  describe('No-op mutations', () => {
    it('treats no-op as unchanged for sharing purposes', () => {
      const shared = { value: 5 }
      const current = { a: shared, b: shared }

      const result = createPatch(current, (draft: typeof current) => {
        draft.a.value = 5 // Same value
        return draft
      })

      // No actual change, so original is preserved
      assert.equal(result.a, shared)
      assert.equal(result.b, shared)
    })
  })

  describe('Return modes and sharing', () => {
    it('returns nested draft with correct sharing', () => {
      const shared = { count: 0 }
      const current = {
        nested: { ref: shared },
        other: shared,
      }

      const result = createPatch(current, (draft: typeof current) => {
        draft.nested.ref.count = 1
        return draft.nested
      })

      assert.deepEqual(result, { ref: { count: 1 } })
    })

    it('returns ordinary object containing draft values', () => {
      const current = { item: { value: 0 } }

      const result = createPatch(current, (draft: typeof current) => {
        draft.item.value = 7
        return { wrapped: draft.item }
      })

      assert.deepEqual(result, { wrapped: { value: 7 } })
    })
  })
})
