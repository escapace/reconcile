import { describe, expect, it } from 'vitest'
import { produce } from '../index'

// A read of a `Date`, buffer, view or URL gives the recipe a copy, which draft searches count as
// the member it copies, as they count a draft as the object it drafts.
const values = (): Array<[string, object]> => [
  ['Date', new Date(5)],
  ['view', new Uint8Array(2)],
  ['URL', new URL('https://a.test/')],
]

describe('searches with a copy of a special value', () => {
  it.each(values())('find and delete a %s member of a Set draft', (_name, value) => {
    const set = new Set<unknown>()
    set.add(value).add(1)
    const current = { set }
    const result = produce(current, (draft) => {
      const member = [...draft.set][0] as object
      expect(member).not.toBe(value)
      expect(draft.set.has(member)).toBe(true)
      // eslint-disable-next-line baseline-js/use-baseline -- the draft's own Set methods
      expect(new Set([member]).isSubsetOf(draft.set)).toBe(true)
      // eslint-disable-next-line baseline-js/use-baseline -- the draft's own Set methods
      expect(draft.set.isSubsetOf(new Set([1, member]))).toBe(true)
      expect(draft.set.delete(member)).toBe(true)
      return draft
    })
    expect([...result.set]).toEqual([1])
    expect(current.set.has(value)).toBe(true)
  })

  it.each(values())(
    'find a %s key of a Map draft through a copy read elsewhere',
    (_name, value) => {
      const current = { list: [value], map: new Map<unknown, number>([[value, 1]]) }
      const result = produce(current, (draft) => {
        const copy = draft.list[0]
        expect(copy).not.toBe(value)
        expect(draft.map.get(copy)).toBe(1)
        draft.map.set(copy, 2)
        return draft
      })
      expect([...result.map]).toEqual([[value, 2]])
    },
  )
})
