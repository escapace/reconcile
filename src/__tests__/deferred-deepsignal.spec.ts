import { deepSignal } from 'alien-deepsignals'
import { assert, describe, it } from 'vitest'

import { reconcile, produce } from '../index'

// Deferred until a public backing-storage identity protocol can satisfy publication.
// eslint-disable-next-line vitest/no-disabled-tests -- User deferred integration; keep executable fixtures.
describe.skip('deferred deepSignal integration', () => {
  it('remains compatible with alien-deepsignals roots', () => {
    const current = deepSignal({
      nested: { count: 0 },
    })

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.nested.count = 8
        return draft
      }),
    )

    assert.equal(result, current)
    assert.equal(result.nested.count, 8)
  })

  it('retains compatible parent identity under alien-deepsignals nested change', () => {
    const current = deepSignal({
      nested: { count: 0 },
      sibling: { keep: true },
    })
    const siblingReference = current.sibling

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.nested.count = 13
        return draft
      }),
    )

    assert.equal(result, current)
    assert.equal(result.sibling, siblingReference)
    assert.equal(result.nested.count, 13)
  })

  it('applies the same identity-reuse rules to alien-deepsignals objects', () => {
    const current = deepSignal({
      nested: { count: 0 },
      sibling: { keep: true },
    })
    const siblingReference = current.sibling

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.nested.count = 5
        return draft
      }),
    )

    assert.equal(result, current)
    assert.equal(result.sibling, siblingReference)
    assert.equal(result.nested.count, 5)
  })
  it('preserves independent storage for raw and wrapped siblings with equal values', () => {
    const raw = { n: 0 }
    const current = { left: raw, right: deepSignal(raw) }
    assert.equal(reconcile(current, { left: { n: 1 }, right: { n: 1 } }), current)
    current.left.n = 2
    assert.equal(current.right.n, 1)
  })
})
