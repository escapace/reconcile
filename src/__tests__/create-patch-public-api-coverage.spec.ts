import { assert, describe, expect, it } from 'vitest'

import { createPatch } from '../index'

class UnsupportedCounter {
  value: number

  constructor(value: number) {
    this.value = value
  }
}

interface CyclicCoverage {
  value: number
  self?: CyclicCoverage
}

interface OrdinaryCyclicRoot {
  self?: unknown
  value?: number
}

interface ReturnedDraftCycleRoot {
  item?: { count: number }
  self?: unknown
}

describe('createPatch public api coverage', () => {
  it('supports primitive current roots without drafting', () => {
    assert.equal(
      createPatch(1, (draft) => draft + 1),
      2,
    )
    assert.equal(
      createPatch('a', (draft) => `${draft}b`),
      'ab',
    )
    assert.equal(
      createPatch(true, (draft) => !draft),
      false,
    )
  })

  it('supports special current roots through clone-on-read semantics', () => {
    const current = new Date('2024-01-01T00:00:00.000Z')

    const result = createPatch(current, (draft) => {
      draft.setUTCFullYear(2025)
      return draft
    })

    assert.notEqual(result, current)
    assert.equal(result.getUTCFullYear(), 2025)
    assert.equal(current.getUTCFullYear(), 2024)
  })

  it('reuses unchanged special current roots when their clone stays semantically equal', () => {
    const currentDate = new Date('2024-01-01T00:00:00.000Z')
    const currentBuffer = new Uint8Array([1, 2, 3, 4]).buffer
    const currentView = new DataView(currentBuffer)
    const currentTyped = new Uint16Array([5, 6, 7])

    const dateResult = createPatch(currentDate, (draft) => draft)
    const bufferResult = createPatch(currentBuffer, (draft) => draft)
    const viewResult = createPatch(currentView, (draft) => draft)
    const typedResult = createPatch(currentTyped, (draft) => draft)

    assert.equal(dateResult, currentDate)
    assert.equal(bufferResult, currentBuffer)
    assert.equal(viewResult, currentView)
    assert.equal(typedResult, currentTyped)
  })

  it('returns changed special current roots when their clone stops being semantically equal', () => {
    const currentBuffer = new Uint8Array([1, 2, 3, 4]).buffer
    const currentView = new DataView(currentBuffer)
    const currentTyped = new Uint16Array([5, 6, 7])

    const bufferResult = createPatch(currentBuffer, (draft) => {
      new Uint8Array(draft)[0] = 9
      return draft
    })
    const viewResult = createPatch(currentView, (draft) => {
      draft.setUint8(1, 8)
      return draft
    })
    const typedResult = createPatch(currentTyped, (draft) => {
      draft[1] = 9
      return draft
    })

    assert.notEqual(bufferResult, currentBuffer)
    assert.deepEqual(Array.from(new Uint8Array(bufferResult)), [9, 2, 3, 4])
    assert.deepEqual(Array.from(new Uint8Array(currentBuffer)), [1, 2, 3, 4])
    assert.notEqual(viewResult, currentView)
    assert.deepEqual(
      Array.from(new Uint8Array(viewResult.buffer, viewResult.byteOffset, viewResult.byteLength)),
      [1, 8, 3, 4],
    )
    assert.deepEqual(
      Array.from(
        new Uint8Array(currentView.buffer, currentView.byteOffset, currentView.byteLength),
      ),
      [1, 2, 3, 4],
    )
    assert.notEqual(typedResult, currentTyped)
    assert.equal(typedResult.constructor, Uint16Array)
    assert.deepEqual(Array.from(typedResult), [5, 9, 7])
    assert.deepEqual(Array.from(currentTyped), [5, 6, 7])
  })

  it('reuses unchanged clone-on-read child references after reading every supported special value kind', () => {
    const sharedBuffer = new Uint8Array([1, 2, 3, 4]).buffer
    const current = {
      buffer: sharedBuffer,
      date: new Date('2024-01-01T00:00:00.000Z'),
      touched: { count: 0 },
      typed: new Uint8Array(sharedBuffer),
      view: new DataView(sharedBuffer, 1, 2),
    }

    const result = createPatch(current, (draft) => {
      assert.notEqual(draft.date, current.date)
      assert.notEqual(draft.buffer, current.buffer)
      assert.notEqual(draft.typed, current.typed)
      assert.notEqual(draft.view, current.view)
      assert.equal(draft.typed.buffer, draft.buffer)
      assert.equal(draft.view.buffer, draft.buffer)

      draft.touched.count = 1
      return draft
    })

    assert.notEqual(result, current)
    assert.equal(result.date, current.date)
    assert.equal(result.buffer, current.buffer)
    assert.equal(result.typed, current.typed)
    assert.equal(result.view, current.view)
    assert.notEqual(result.touched, current.touched)
    assert.equal(result.touched.count, 1)
    assert.equal(current.touched.count, 0)
  })

  it('supports reflective object-draft operations through the public recipe surface', () => {
    const current = {
      child: { count: 0 },
      value: 1,
    }

    const result = createPatch(current, (draft) => {
      expect('child' in draft).toBe(true)
      expect(Reflect.ownKeys(draft)).toEqual(['child', 'value'])
      expect(Object.getPrototypeOf(draft)).toBe(Object.getPrototypeOf(current))

      const beforeAccess = Object.getOwnPropertyDescriptor(draft, 'child')
      expect(beforeAccess).toBeDefined()
      expect(beforeAccess?.value).toBe(current.child)

      void draft.child

      const afterAccess = Object.getOwnPropertyDescriptor(draft, 'child')
      expect(afterAccess).toBeDefined()
      expect(afterAccess?.value).not.toBe(current.child)

      draft.value = 2
      return draft
    })

    assert.equal(result.child, current.child)
    assert.equal(result.value, 2)
  })

  it('supports Object.keys on plain-object drafts without materializing child values', () => {
    const current = {
      child: { count: 0 },
      value: 1,
    }

    const result = createPatch(current, (draft) => {
      expect(Object.keys(draft)).toEqual(['child', 'value'])

      const descriptor = Object.getOwnPropertyDescriptor(draft, 'child')
      expect(descriptor).toBeDefined()
      expect(descriptor?.value).toBe(current.child)

      draft.value = 2
      return draft
    })

    assert.equal(result.child, current.child)
    assert.equal(result.value, 2)
  })

  it('supports Object.values and Object.entries on plain-object drafts with draft-side values', () => {
    const current = {
      child: { count: 0 },
      date: new Date('2024-01-01T00:00:00.000Z'),
      value: 1,
    }

    const result = createPatch(current, (draft) => {
      const values = Object.values(draft) as [{ count: number }, Date, number]

      expect(values[0]).not.toBe(current.child)
      expect(values[1]).not.toBe(current.date)
      expect(values[2]).toBe(1)

      values[0].count = 2
      values[1].setUTCFullYear(2025)

      const entries = Object.entries(draft) as Array<
        ['child', { count: number }] | ['date', Date] | ['value', number]
      >

      expect(entries.map(([key]) => key)).toEqual(['child', 'date', 'value'])
      expect(entries[0][1]).toBe(values[0])
      expect(entries[1][1]).toBe(values[1])
      expect(entries[2][1]).toBe(1)

      return draft
    })

    assert.notEqual(result.child, current.child)
    assert.deepEqual(result.child, { count: 2 })
    assert.notEqual(result.date, current.date)
    assert.equal(result.date.getUTCFullYear(), 2025)
    assert.equal(result.value, 1)
    assert.deepEqual(current.child, { count: 0 })
    assert.equal(current.date.getUTCFullYear(), 2024)
  })

  it('uses the draft-shaped receiver for a user-provided plain-object Symbol.iterator', () => {
    const current = {
      child: { count: 0 },
      date: new Date('2024-01-01T00:00:00.000Z'),
      *[Symbol.iterator](): Generator<Date | { count: number }, void, undefined> {
        assert.notEqual(this, current)
        yield (this as { child: { count: number } }).child
        yield (this as { date: Date }).date
      },
    }

    const result = createPatch(current, (draft) => {
      const [child, date] = Array.from(draft as unknown as Iterable<Date | { count: number }>) as [
        { count: number },
        Date,
      ]

      assert.notEqual(child, current.child)
      assert.notEqual(date, current.date)

      child.count = 3
      date.setUTCFullYear(2025)
      return draft
    })

    assert.notEqual(result.child, current.child)
    assert.deepEqual(result.child, { count: 3 })
    assert.notEqual(result.date, current.date)
    assert.equal(result.date.getUTCFullYear(), 2025)
    assert.deepEqual(current.child, { count: 0 })
    assert.equal(current.date.getUTCFullYear(), 2024)
  })

  it('preserves accessor semantics when modifying an object with accessor properties', () => {
    const accessed = {
      _count: 1,
      touched: 0,
      get count() {
        return this._count
      },
      set count(next: number) {
        this._count = next
      },
    }
    const current = { accessed }

    const result = createPatch(current, (draft) => {
      draft.accessed.touched = 1
      return draft
    })

    assert.notEqual(result.accessed, current.accessed)
    assert.equal(result.accessed.count, 1)
    result.accessed.count = 2
    assert.equal(result.accessed.count, 2)
    assert.equal(current.accessed.count, 1)
    assert.equal(result.accessed.touched, 1)
  })

  it('supports inherited object-valued properties through plain-object drafts', () => {
    const shared = { count: 0 }
    const prototype = { inherited: shared }
    const current = Object.create(prototype) as {
      inherited: { count: number }
      local: number
    }

    current.local = 1

    const result = createPatch(current, (draft) => {
      expect('inherited' in draft).toBe(true)
      expect(Reflect.ownKeys(draft)).toEqual(['local'])

      const first = draft.inherited
      const second = draft.inherited

      expect(first).toBe(second)
      expect(first).not.toBe(shared)

      first.count = 2

      return {
        inherited: draft.inherited,
        local: draft.local,
      }
    })

    assert.equal(result.local, 1)
    assert.notEqual(result.inherited, shared)
    assert.equal(result.inherited.count, 2)
    assert.equal(shared.count, 0)
  })

  it('supports inherited special clone-on-read values through plain-object drafts', () => {
    const sharedDate = new Date('2024-01-01T00:00:00.000Z')
    const prototype = { inheritedDate: sharedDate }
    const current = Object.create(prototype) as {
      inheritedDate: Date
      touched: { count: number }
    }

    current.touched = { count: 0 }

    const result = createPatch(current, (draft) => {
      expect('inheritedDate' in draft).toBe(true)
      expect(Reflect.ownKeys(draft)).toEqual(['touched'])

      const first = draft.inheritedDate
      const second = draft.inheritedDate

      expect(first).toBe(second)
      expect(first).not.toBe(sharedDate)

      first.setUTCFullYear(2025)
      draft.touched.count = 1

      return {
        inheritedDate: draft.inheritedDate,
        touched: draft.touched,
      }
    })

    assert.notEqual(result.inheritedDate, sharedDate)
    assert.equal(result.inheritedDate.getUTCFullYear(), 2025)
    assert.equal(sharedDate.getUTCFullYear(), 2024)
    assert.equal(result.touched.count, 1)
    assert.equal(current.touched.count, 0)
  })

  it('treats empty map clear, missing delete, and missing get as no-op paths', () => {
    const current = new Map<string, number>()

    const result = createPatch(current, (draft) => {
      expect(draft.get('missing')).toBeUndefined()
      expect(draft.delete('missing')).toBe(false)
      draft.clear()
      return draft
    })

    expect(result).toBe(current)
  })

  it('treats duplicate set add, empty clear, and missing delete as no-op paths when content does not change', () => {
    const current = new Set<number>([1])

    const result = createPatch(current, (draft) => {
      draft.add(1)
      expect(draft.delete(2)).toBe(false)
      return draft
    })

    expect(result).toBe(current)

    const emptyCurrent = new Set<number>()
    const emptyResult = createPatch(emptyCurrent, (draft) => {
      draft.clear()
      return draft
    })

    expect(emptyResult).toBe(emptyCurrent)
  })

  it('reuses one finalized image when a draft handle and its original base both appear in an ordinary returned root', () => {
    const current = {
      item: { count: 0 },
    }

    const result = createPatch(current, (draft) => {
      draft.item.count = 2

      return {
        fromBase: current.item,
        fromDraft: draft.item,
      }
    })

    expect(result.fromDraft).toBe(result.fromBase)
    expect(result.fromDraft).not.toBe(current.item)
    expect(result).toEqual({
      fromBase: { count: 2 },
      fromDraft: { count: 2 },
    })
  })

  it('keeps one stable draft-side special clone across repeated reads of the same property', () => {
    const current = {
      date: new Date('2024-01-01T00:00:00.000Z'),
    }

    const result = createPatch(current, (draft) => {
      const first = draft.date
      const second = draft.date

      expect(first).toBe(second)
      first.setUTCFullYear(2025)

      return {
        left: first,
        right: second,
      }
    })

    expect(result.left).toBe(result.right)
    expect(result.left.getUTCFullYear()).toBe(2025)
    expect(current.date.getUTCFullYear()).toBe(2024)
  })

  it('reuses cached special clones when the same special child is reached through repeated aliases', () => {
    const sharedDate = new Date('2024-01-01T00:00:00.000Z')
    const current = {
      left: sharedDate,
      right: sharedDate,
      touched: { count: 0 },
    }

    const result = createPatch(current, (draft) => {
      void draft.left
      void draft.right
      draft.touched.count = 1
      return draft
    })

    expect(result.left).toBe(result.right)
    expect(result.left).toBe(sharedDate)
    expect(result.touched.count).toBe(1)
    expect(current.touched.count).toBe(0)
  })

  it('keeps one stable map wrapper across repeated reads of the same property', () => {
    const current = {
      map: new Map<string, { count: number }>([['item', { count: 0 }]]),
    }

    const result = createPatch(current, (draft) => {
      const first = draft.map
      const second = draft.map

      expect(first).toBe(second)
      first.get('item')!.count = 1

      return {
        left: first,
        right: second,
      }
    })

    expect(result.left).toBe(result.right)
    expect(result.left.get('item')).toEqual({ count: 1 })
    expect(current.map.get('item')).toEqual({ count: 0 })
  })

  it('supports repeated map aliases and mixed map value kinds through the public recipe surface', () => {
    const shared = new Map<string, unknown>([
      ['object', { count: 0 }],
      ['opaque', new UnsupportedCounter(2)],
      ['primitive', 1],
      ['special', new Date('2024-01-01T00:00:00.000Z')],
    ])
    const current = {
      left: shared,
      right: shared,
    }

    const result = createPatch(current, (draft) => {
      expect(draft.left).toBe(draft.right)
      expect(draft.right.size).toBe(4)
      expect(draft.left.has('primitive')).toBe(true)
      expect(draft.left.get('missing')).toBeUndefined()
      expect(draft.left.get('primitive')).toBe(1)
      expect(draft.left.get('special')).toBe(draft.left.get('special'))
      expect((draft.left.get('opaque') as UnsupportedCounter).value).toBe(2)
      ;(draft.left.get('object') as { count: number }).count = 3
      return draft
    })

    expect(result.left).toBe(result.right)
    expect(result.left.size).toBe(4)
    expect(result.left.get('primitive')).toBe(1)
    expect((result.left.get('opaque') as UnsupportedCounter).value).toBe(2)
    expect(result.left.get('object')).toEqual({ count: 3 })
  })

  it('supports repeated set aliases through the public recipe surface', () => {
    const shared = new Set<object>()
    const current = {
      item: { id: 1 },
      left: shared,
      right: shared,
    }

    const result = createPatch(current, (draft) => {
      draft.left.add(draft.item)
      expect(draft.right.has(draft.item)).toBe(true)
      return draft
    })

    expect(result.left).toBe(result.right)
    expect(Array.from(result.left.values())).toEqual([{ id: 1 }])
  })

  it('normalizes already-drafted base objects, maps, and sets in set membership operations', () => {
    const objectValue = { id: 1 }
    const mapValue = new Map<string, number>([['k', 1]])
    const setValue = new Set<number>([2])
    const current = {
      mapValue,
      objectValue,
      outer: new Set<object>([mapValue, objectValue, setValue]),
      setValue,
    }

    const result = createPatch(current, (draft) => {
      void draft.objectValue
      void draft.mapValue
      void draft.setValue

      expect(draft.outer.has(current.objectValue)).toBe(true)
      expect(draft.outer.has(current.mapValue)).toBe(true)
      expect(draft.outer.has(current.setValue)).toBe(true)

      expect(draft.outer.delete(current.objectValue)).toBe(true)
      expect(draft.outer.delete(current.mapValue)).toBe(true)
      expect(draft.outer.delete(current.setValue)).toBe(true)

      draft.outer.add(current.objectValue)
      draft.outer.add(current.mapValue)
      draft.outer.add(current.setValue)

      return draft
    })

    expect(result.outer.has(result.objectValue)).toBe(true)
    expect(result.outer.has(result.mapValue)).toBe(true)
    expect(result.outer.has(result.setValue)).toBe(true)
  })

  it('rebuilds an open ordinary map key when it points into a touched region', () => {
    const touched = { count: 0 }
    const key = { child: touched }
    const current = {
      key,
      touched,
    }

    const result = createPatch(current, (draft) => {
      draft.touched.count = 4
      return {
        map: new Map<object, string>([[key, 'value']]),
        touched: draft.touched,
      }
    })

    const [resultKey] = Array.from(result.map.keys()) as Array<{ child: { count: number } }>
    assert.notEqual(resultKey, key)
    assert.equal(resultKey.child, result.touched)
    assert.notEqual(resultKey.child, current.touched)
    assert.equal(key.child, current.touched)
  })

  it('preserves sparse-array holes on no-op current-root reads', () => {
    const current = [] as Array<string | undefined>
    current[2] = 'v2'

    const result = createPatch(current, (draft) => draft)

    expect(result).toBe(current)
    expect(result.length).toBe(3)
    expect(0 in result).toBe(false)
    expect(1 in result).toBe(false)
    expect(2 in result).toBe(true)
  })

  it('publishes nested array-element mutations from an array root', () => {
    const current = [{ count: 0 }]

    const result = createPatch(current, (draft) => {
      draft[0].count = 1
      return draft
    })

    expect(result).toEqual([{ count: 1 }])
    expect(result).not.toBe(current)
    expect(result[0]).not.toBe(current[0])
    expect(current).toEqual([{ count: 0 }])
  })

  it('reuses unchanged array roots after reading a drafted child slot', () => {
    const child = { count: 0 }
    const current = [child]

    const result = createPatch(current, (draft) => {
      expect(draft[0]).not.toBe(child)
      return draft
    })

    expect(result).toBe(current)
    expect(result[0]).toBe(child)
  })

  it('publishes nested array-element mutations from a nested array draft root', () => {
    const current = {
      items: [{ count: 0 }],
    }

    const result = createPatch(current, (draft) => {
      draft.items[0].count = 2
      return draft.items
    })

    expect(result).toEqual([{ count: 2 }])
    expect(result).not.toBe(current.items)
    expect(result[0]).not.toBe(current.items[0])
    expect(current).toEqual({ items: [{ count: 0 }] })
  })

  it('reuses unchanged nested array draft roots after reading a drafted child slot', () => {
    const child = { count: 0 }
    const current = {
      items: [child],
    }

    const result = createPatch(current, (draft) => {
      expect(draft.items[0]).not.toBe(child)
      return draft.items
    })

    expect(result).toBe(current.items)
    expect(result[0]).toBe(child)
  })

  it('reuses cyclic current roots on no-op reads', () => {
    const current: CyclicCoverage = { value: 1 }
    current.self = current

    const result = createPatch(current, (draft) => draft)

    expect(result).toBe(current)
    expect(result.self).toBe(current)
  })

  it('reuses cyclic current roots after self-referential draft access', () => {
    const current: CyclicCoverage = { value: 1 }
    current.self = current

    const result = createPatch(current, (draft) => {
      expect(draft.self).toBe(draft)
      return draft
    })

    expect(result).toBe(current)
    expect(result.self).toBe(current)
  })

  it('returns ordinary cyclic roots unchanged when they do not require finalization', () => {
    const returned: OrdinaryCyclicRoot = {}
    returned.self = returned
    returned.value = 1

    const result = createPatch(0, () => returned)

    expect(result).toBe(returned)
    expect(result.self).toBe(returned)
    expect(result.value).toBe(1)
  })

  it('finalizes ordinary returned roots with cycles when another branch contains a draft value', () => {
    const current = {
      item: { count: 0 },
    }

    const result = createPatch(current, (draft) => {
      draft.item.count = 5

      const returned: ReturnedDraftCycleRoot = {}

      returned.self = returned
      returned.item = draft.item
      return returned
    })

    expect(result.item).toEqual({ count: 5 })
    expect(result.self).toBe(result)
  })

  it('finalizes fresh special values inside an ordinary returned root when another child forces root finalization', () => {
    const current = {
      item: { count: 0 },
    }
    const date = new Date('2024-01-01T00:00:00.000Z')
    const buffer = new Uint8Array([1, 2, 3, 4]).buffer
    const typed = new Uint16Array(buffer, 0, 2)
    const view = new DataView(buffer, 1, 2)

    const result = createPatch(current, (draft) => {
      draft.item.count = 1

      return {
        buffer,
        date,
        item: draft.item,
        typed,
        view,
      }
    }) as {
      buffer: ArrayBuffer
      date: Date
      item: { count: number }
      typed: Uint16Array
      view: DataView
    }

    expect(result.item).toEqual({ count: 1 })
    expect(result.date).not.toBe(date)
    expect(result.date.getTime()).toBe(date.getTime())
    expect(result.buffer).not.toBe(buffer)
    expect(Array.from(new Uint8Array(result.buffer))).toEqual([1, 2, 3, 4])
    expect(result.typed).not.toBe(typed)
    expect(result.typed.constructor).toBe(Uint16Array)
    expect(Array.from(result.typed)).toEqual([513, 1027])
    expect(result.view).not.toBe(view)
    expect(result.view.byteOffset).toBe(1)
    expect(result.view.byteLength).toBe(2)
    expect(result.typed.buffer).toBe(result.buffer)
    expect(result.view.buffer).toBe(result.buffer)
    expect(
      Array.from(
        new Uint8Array(result.view.buffer, result.view.byteOffset, result.view.byteLength),
      ),
    ).toEqual([2, 3])
  })
})
