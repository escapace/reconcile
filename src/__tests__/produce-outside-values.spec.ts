import { assert, describe, it } from 'vitest'
import { produce } from '../index'

// An unchanged value stays itself whether it comes from `current` or the recipe assigns it from
// outside; a linked URL and its `searchParams`, or a buffer and its views, are copied together
// only when the recipe changes one of them.

describe('produce keeps unchanged outside values', () => {
  it('keeps a URL assigned next to its searchParams from current', () => {
    const url = new URL('https://example.test/?a=1')
    const current = { params: url.searchParams }
    const result = produce(current, (draft) => ({ ...draft, url }))
    assert.strictEqual(result.url, url)
    assert.strictEqual(result.params, url.searchParams)
  })

  it('keeps searchParams assigned next to their URL from current', () => {
    const url = new URL('https://example.test/?a=1')
    const result = produce({ url }, (draft) => ({ ...draft, params: url.searchParams }))
    assert.strictEqual(result.url, url)
    assert.strictEqual(result.params, result.url.searchParams)
  })

  it('copies the URL with its params when the recipe changes the params', () => {
    const url = new URL('https://example.test/?a=1')
    const current = { params: url.searchParams }
    const result = produce(current, (draft) => {
      draft.params.append('b', '2')
      return { ...draft, url }
    })
    assert.notStrictEqual(result.url, url)
    assert.strictEqual(result.url.searchParams, result.params)
    assert.equal(result.url.href, 'https://example.test/?a=1&b=2')
    assert.equal(url.href, 'https://example.test/?a=1')
  })

  for (const make of [
    () => new Date(1),
    () => new ArrayBuffer(2),
    () => new Uint8Array(2),
    () => new DataView(new ArrayBuffer(2)),
    () => new URL('https://example.test/'),
    () => new URLSearchParams('a=1'),
  ]) {
    const name = Object.prototype.toString.call(make())
    it(`keeps an assigned ${name} and copies it only when the recipe changes it`, () => {
      const value = make()
      const state: { count: number; value?: object } = { count: 0 }
      const kept = produce(state, (draft) => {
        draft.value = value
        draft.count = 1
        return draft
      })
      assert.strictEqual(kept.value, value)
      const returned = produce({ count: 0 }, () => ({ value }))
      assert.strictEqual(returned.value, value)
    })
  }

  it('copies an assigned value that the recipe then changes, leaving the original', () => {
    const date = new Date(1)
    const state: { date?: Date } = {}
    const result = produce(state, (draft) => {
      draft.date = date
      draft.date.setTime(5)
      return draft
    })
    assert.equal(result.date!.getTime(), 5)
    assert.equal(date.getTime(), 1)
  })

  it('keeps a view assigned over a buffer from current, and the link between them', () => {
    const buffer = new ArrayBuffer(4)
    const state: { buffer: ArrayBuffer; view?: Uint8Array } = { buffer }
    const result = produce(state, (draft) => {
      draft.view = new Uint8Array(buffer)
      return draft
    })
    assert.strictEqual(result.buffer, buffer)
    assert.strictEqual(result.view!.buffer, result.buffer)
  })

  it('keeps aliases of one outside value as one value', () => {
    const date = new Date(1)
    const result = produce({ count: 0 }, () => ({ left: date, nested: { right: date } }))
    assert.strictEqual(result.left, date)
    assert.strictEqual(result.nested.right, date)
  })
})
