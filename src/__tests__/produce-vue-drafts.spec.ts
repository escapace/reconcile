import { assert, describe, it } from 'vitest'
import { effect, isProxy, isReactive, isReadonly, reactive, readonly, toRaw } from 'vue'
import { produce } from '../index'

// A draft reads its own properties from its object and every other property from its prototype,
// before and after its first write, so a Vue proxy never answers a draft read with its markers
// or its versions of array methods. lean/Produce/DraftRead.lean states the rule and
// check-draft-read-runtime.ts compares it natively.

describe('drafts of Vue state are not Vue state', () => {
  it('reports no Vue markers, before and after the first write', () => {
    for (const wrap of [reactive, readonly]) {
      const state = wrap({ list: [{ n: 1 }], obj: { n: 1 } }) as {
        list: Array<{ n: number }>
        obj: { n: number }
      }
      produce(state, (draft) => {
        for (const written of [false, true]) {
          if (written) draft.obj.n = 2
          for (const value of [draft.obj, draft.list, draft.list[0]]) {
            assert.isFalse(isReactive(value) || isReadonly(value))
            assert.strictEqual(toRaw(value), value)
          }
        }
        return draft
      })
    }
  })

  it('gives array methods drafts, so a recipe never changes current or runs its effects', () => {
    const state = reactive({ list: [{ n: 1 }, { n: 2 }] })
    let runs = 0
    effect(() => {
      void state.list[0].n
      runs += 1
    })
    const result = produce(state, (draft) => {
      draft.list.forEach((item) => {
        item.n += 10
      })
      const found = draft.list.find((item) => item.n === 12)
      assert.strictEqual(found, draft.list[1])
      for (const item of draft.list) assert.isFalse(isProxy(item))
      return draft
    })
    assert.deepEqual(
      result.list.map((item) => item.n),
      [11, 12],
    )
    assert.deepEqual(
      toRaw(state).list.map((item) => item.n),
      [1, 2],
    )
    assert.equal(runs, 1)
  })
})

describe('Vue proxies of drafts', () => {
  it('finishes when the recipe stores reactive(draft) in the draft', () => {
    const state = reactive({ x: { n: 1 } })
    const result = produce(state, (draft) => {
      ;(draft as Record<string, unknown>).y = reactive(draft)
      return draft
    }) as Record<string, unknown>
    assert.deepEqual(Object.keys(result), ['x', 'y'])
  })

  it('writes through reactive(draft) into the draft', () => {
    const current = { x: { n: 1 } }
    const result = produce(current, (draft) => {
      reactive(draft.x).n = 2
      assert.equal(draft.x.n, 2)
      return draft
    })
    assert.deepEqual(result.x, { n: 2 })
    assert.equal(current.x.n, 1)
  })
})
