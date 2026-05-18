import { assert, describe, it } from 'vitest'

import { createPatch } from '../patch'

const bytesOf = (value: ArrayBufferLike): number[] => Array.from(new Uint8Array(value))
const viewBytesOf = (value: ArrayBufferView): number[] =>
  Array.from(new Uint8Array(value.buffer, value.byteOffset, value.byteLength))

describe('clone-on-read sibling-write contract', () => {
  it('preserves an unread Date by identity when only a sibling is drafted', () => {
    const date = new Date('2024-01-01T00:00:00.000Z')
    const current = {
      date,
      touched: { count: 0 },
    }

    const result = createPatch(current, (draft) => {
      draft.touched.count = 1
      return draft
    })

    assert.notEqual(result, current)
    assert.notEqual(result.touched, current.touched)
    assert.equal(result.date, date)
    assert.equal(result.date.getTime(), date.getTime())
  })

  it('preserves an unread ArrayBuffer by identity when only a sibling is drafted', () => {
    const buffer = new Uint8Array([1, 2, 3, 4]).buffer
    const current = {
      buffer,
      touched: { count: 0 },
    }

    const result = createPatch(current, (draft) => {
      draft.touched.count = 1
      return draft
    })

    assert.notEqual(result, current)
    assert.notEqual(result.touched, current.touched)
    assert.equal(result.buffer, buffer)
    assert.deepEqual(bytesOf(result.buffer), [1, 2, 3, 4])
  })

  it('preserves an unread DataView by identity when only a sibling is drafted', () => {
    const buffer = new Uint8Array([1, 2, 3, 4]).buffer
    const view = new DataView(buffer, 1, 2)
    const current = {
      touched: { count: 0 },
      view,
    }

    const result = createPatch(current, (draft) => {
      draft.touched.count = 1
      return draft
    })

    assert.notEqual(result, current)
    assert.notEqual(result.touched, current.touched)
    assert.equal(result.view, view)
    assert.equal(result.view.buffer, buffer)
    assert.equal(result.view.byteOffset, 1)
    assert.equal(result.view.byteLength, 2)
    assert.deepEqual(viewBytesOf(result.view), [2, 3])
  })

  it('preserves an unread typed array by identity when only a sibling is drafted', () => {
    const typed = new Uint16Array([1, 2, 3, 4])
    const current = {
      touched: { count: 0 },
      typed,
    }

    const result = createPatch(current, (draft) => {
      draft.touched.count = 1
      return draft
    })

    assert.notEqual(result, current)
    assert.notEqual(result.touched, current.touched)
    assert.equal(result.typed, typed)
    assert.equal(result.typed.buffer, typed.buffer)
    assert.equal(result.typed.byteOffset, typed.byteOffset)
    assert.equal(result.typed.byteLength, typed.byteLength)
    assert.deepEqual(Array.from(result.typed), [1, 2, 3, 4])
  })

  it('preserves unread shared clone-on-read references by identity when only a sibling is drafted', () => {
    const date = new Date('2024-01-01T00:00:00.000Z')
    const buffer = new Uint8Array([1, 2, 3, 4]).buffer
    const view = new DataView(buffer, 1, 2)
    const typed = new Uint8Array(buffer)
    const current = {
      bufferLeft: buffer,
      bufferRight: buffer,
      dateLeft: date,
      dateRight: date,
      touched: { count: 0 },
      typedLeft: typed,
      typedRight: typed,
      viewLeft: view,
      viewRight: view,
    }

    const result = createPatch(current, (draft) => {
      draft.touched.count = 1
      return draft
    })

    assert.equal(result.dateLeft, date)
    assert.equal(result.dateRight, date)
    assert.equal(result.dateLeft, result.dateRight)
    assert.equal(result.bufferLeft, buffer)
    assert.equal(result.bufferRight, buffer)
    assert.equal(result.bufferLeft, result.bufferRight)
    assert.equal(result.viewLeft, view)
    assert.equal(result.viewRight, view)
    assert.equal(result.viewLeft, result.viewRight)
    assert.equal(result.typedLeft, typed)
    assert.equal(result.typedRight, typed)
    assert.equal(result.typedLeft, result.typedRight)
  })

  it('preserves unread buffer/view aliases by identity when only a sibling is drafted', () => {
    const buffer = new Uint8Array([1, 2, 3, 4]).buffer
    const typed = new Uint8Array(buffer)
    const view = new DataView(buffer, 1, 2)
    const current = {
      buffer,
      touched: { count: 0 },
      typed,
      view,
    }

    const result = createPatch(current, (draft) => {
      draft.touched.count = 1
      return draft
    })

    assert.equal(result.buffer, buffer)
    assert.equal(result.typed, typed)
    assert.equal(result.view, view)
    assert.equal(result.typed.buffer, buffer)
    assert.equal(result.view.buffer, buffer)
  })

  it('does not reuse a read typed-array view when a sibling view changes its backing buffer', () => {
    const buffer = new Uint8Array([1, 2, 3, 4]).buffer
    const current = {
      left: new Uint8Array(buffer, 0, 2),
      right: new Uint8Array(buffer, 2, 2),
    }

    const result = createPatch(current, (draft) => {
      void draft.left
      draft.right[0] = 9
      return draft
    })

    assert.notEqual(result.left, current.left)
    assert.notEqual(result.right, current.right)
    assert.equal(result.left.buffer, result.right.buffer)
    assert.deepEqual(Array.from(result.left), [1, 2])
    assert.deepEqual(Array.from(result.right), [9, 4])
    assert.deepEqual(bytesOf(result.left.buffer), [1, 2, 9, 4])
    assert.deepEqual(bytesOf(buffer), [1, 2, 3, 4])
  })

  it('does not reuse a read DataView when a sibling view changes its backing buffer', () => {
    const buffer = new Uint8Array([1, 2, 3, 4]).buffer
    const current = {
      left: new DataView(buffer, 0, 2),
      right: new Uint8Array(buffer, 2, 2),
    }

    const result = createPatch(current, (draft) => {
      void draft.left
      draft.right[0] = 9
      return draft
    })

    assert.notEqual(result.left, current.left)
    assert.notEqual(result.right, current.right)
    assert.equal(result.left.buffer, result.right.buffer)
    assert.deepEqual(viewBytesOf(result.left), [1, 2])
    assert.deepEqual(Array.from(result.right), [9, 4])
    assert.deepEqual(bytesOf(result.left.buffer), [1, 2, 9, 4])
    assert.deepEqual(bytesOf(buffer), [1, 2, 3, 4])
  })

  it('preserves clone-on-read values inside a draft-managed array rebuilt for a sibling mutation', () => {
    const date = new Date('2024-01-01T00:00:00.000Z')
    const buffer = new Uint8Array([1, 2, 3, 4]).buffer
    const view = new DataView(buffer, 1, 2)
    const typed = new Uint8Array(buffer)
    const touched = { count: 0 }
    const current = [date, buffer, view, typed, touched] as [
      Date,
      ArrayBuffer,
      DataView,
      Uint8Array,
      typeof touched,
    ]

    const result = createPatch(current, (draft) => {
      draft[4].count = 1
      return draft
    })

    assert.notEqual(result, current)
    assert.equal(result[0], date)
    assert.equal(result[1], buffer)
    assert.equal(result[2], view)
    assert.equal(result[3], typed)
    assert.notEqual(result[4], touched)
    assert.deepEqual(result[4], { count: 1 })
  })

  it('preserves clone-on-read map keys and values in a draft-managed map rebuilt for a sibling mutation', () => {
    const dateKey = new Date('2024-01-01T00:00:00.000Z')
    const bufferKey = new Uint8Array([1, 2, 3, 4]).buffer
    const valueDate = new Date('2025-01-01T00:00:00.000Z')
    const valueTyped = new Uint8Array([5, 6, 7, 8])
    const touched = { count: 0 }
    const current = new Map<unknown, unknown>([
      ['touched', touched],
      [bufferKey, valueTyped],
      [dateKey, valueDate],
    ])

    const result = createPatch(current, (draft) => {
      ;(draft.get('touched') as typeof touched).count = 1
      return draft
    })

    assert.notEqual(result, current)
    assert.equal(result.get(dateKey), valueDate)
    assert.equal(result.get(bufferKey), valueTyped)
    assert.notEqual(result.get('touched'), touched)
    assert.deepEqual(result.get('touched'), { count: 1 })
  })

  it('preserves clone-on-read set entries in a draft-managed set rebuilt by a sibling insertion', () => {
    const date = new Date('2024-01-01T00:00:00.000Z')
    const buffer = new Uint8Array([1, 2, 3, 4]).buffer
    const view = new DataView(buffer, 1, 2)
    const typed = new Uint8Array(buffer)
    const current = new Set<unknown>([buffer, date, typed, view])

    const inserted = { count: 1 }
    const result = createPatch(current, (draft) => {
      draft.add(inserted)
      return draft
    })

    assert.notEqual(result, current)
    assert.equal(result.has(date), true)
    assert.equal(result.has(buffer), true)
    assert.equal(result.has(view), true)
    assert.equal(result.has(typed), true)
    assert.equal(result.has(inserted), true)
  })

  it('preserves clone-on-read values inside a current-backed plain object rebuilt for a shared descendant', () => {
    const date = new Date('2024-01-01T00:00:00.000Z')
    const buffer = new Uint8Array([1, 2, 3, 4]).buffer
    const view = new DataView(buffer, 1, 2)
    const typed = new Uint8Array(buffer)
    const touched = { count: 0 }
    const current = {
      nested: { buffer, date, touched, typed, view },
      touched,
    }

    const result = createPatch(current, (draft) => {
      draft.touched.count = 1
      return draft
    })

    assert.notEqual(result.nested, current.nested)
    assert.equal(result.nested.touched, result.touched)
    assert.equal(result.nested.date, date)
    assert.equal(result.nested.buffer, buffer)
    assert.equal(result.nested.view, view)
    assert.equal(result.nested.typed, typed)
  })

  it('preserves clone-on-read values inside a current-backed array rebuilt for a shared descendant', () => {
    const date = new Date('2024-01-01T00:00:00.000Z')
    const buffer = new Uint8Array([1, 2, 3, 4]).buffer
    const view = new DataView(buffer, 1, 2)
    const typed = new Uint8Array(buffer)
    const touched = { count: 0 }
    const current = {
      list: [date, buffer, view, typed, touched] as [
        Date,
        ArrayBuffer,
        DataView,
        Uint8Array,
        typeof touched,
      ],
      touched,
    }

    const result = createPatch(current, (draft) => {
      draft.touched.count = 1
      return draft
    })

    assert.notEqual(result.list, current.list)
    assert.equal(result.list[4], result.touched)
    assert.equal(result.list[0], date)
    assert.equal(result.list[1], buffer)
    assert.equal(result.list[2], view)
    assert.equal(result.list[3], typed)
  })

  it('preserves clone-on-read map keys and values in a current-backed map rebuilt for a shared descendant', () => {
    const dateKey = new Date('2024-01-01T00:00:00.000Z')
    const bufferKey = new Uint8Array([1, 2, 3, 4]).buffer
    const valueDate = new Date('2025-01-01T00:00:00.000Z')
    const valueTyped = new Uint8Array([5, 6, 7, 8])
    const touched = { count: 0 }
    const map = new Map<unknown, unknown>([
      ['touched', touched],
      [bufferKey, valueTyped],
      [dateKey, valueDate],
    ])
    const current = { map, touched }

    const result = createPatch(current, (draft) => {
      draft.touched.count = 1
      return draft
    })

    assert.notEqual(result.map, map)
    assert.equal(result.map.get(dateKey), valueDate)
    assert.equal(result.map.get(bufferKey), valueTyped)
    assert.equal(result.map.get('touched'), result.touched)
  })

  it('preserves clone-on-read set entries in a current-backed set rebuilt for a shared descendant', () => {
    const date = new Date('2024-01-01T00:00:00.000Z')
    const buffer = new Uint8Array([1, 2, 3, 4]).buffer
    const view = new DataView(buffer, 1, 2)
    const typed = new Uint8Array(buffer)
    const touched = { count: 0 }
    const set = new Set<unknown>([buffer, date, touched, typed, view])
    const current = { set, touched }

    const result = createPatch(current, (draft) => {
      draft.touched.count = 1
      return draft
    })

    assert.notEqual(result.set, set)
    assert.equal(result.set.has(date), true)
    assert.equal(result.set.has(buffer), true)
    assert.equal(result.set.has(view), true)
    assert.equal(result.set.has(typed), true)
    assert.equal(result.set.has(result.touched), true)
  })

  it('continues to clone clone-on-read values placed into an ordinary returned root', () => {
    const date = new Date('2024-01-01T00:00:00.000Z')
    const buffer = new Uint8Array([1, 2, 3, 4]).buffer
    const view = new DataView(buffer, 1, 2)
    const typed = new Uint8Array(buffer)
    const current = {
      buffer,
      date,
      item: { count: 0 },
      typed,
      view,
    }

    const result = createPatch(current, (draft) => {
      draft.item.count = 1
      return { buffer, date, item: draft.item, typed, view }
    })

    assert.notEqual(result.date, date)
    assert.notEqual(result.buffer, buffer)
    assert.notEqual(result.view, view)
    assert.notEqual(result.typed, typed)
    assert.equal(result.view.buffer, result.buffer)
    assert.equal(result.typed.buffer, result.buffer)
    assert.deepEqual(result.item, { count: 1 })
    assert.deepEqual(bytesOf(buffer), [1, 2, 3, 4])
  })
})
