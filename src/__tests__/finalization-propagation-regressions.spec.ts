import { assert, describe, it } from 'vitest'
import { createPatch } from '../index'

describe('finalization dependency propagation', () => {
  for (const dataView of [false, true]) {
    for (const reverse of [false, true]) {
      it(`rebinds unread views when a replacement clones their buffer (DataView: ${dataView}, reverse: ${reverse})`, () => {
        const buffer = new ArrayBuffer(4)
        const view = dataView ? new DataView(buffer, 1, 2) : new Uint8Array(buffer, 1, 2)
        const current = { nested: { view } }
        const result = createPatch(current, (draft) =>
          reverse ? { ...{ root: draft }, buffer } : { buffer, root: draft },
        )
        assert.equal(result.buffer, result.root.nested.view.buffer)
        assert.equal(result.root.nested.view.byteOffset, 1)
        assert.equal(result.root.nested.view.byteLength, 2)
        new Uint8Array(result.buffer)[1] = 9
        assert.equal(new Uint8Array(result.root.nested.view.buffer)[1], 9)
        assert.equal(new Uint8Array(buffer)[1], 0)
      })
    }
  }

  it('processes long sharing chains without repeatedly scanning the entire graph', () => {
    const length = 300
    const dates = Array.from({ length: length + 1 }, (_, index) => new Date(index))
    let scans = 0
    const entries = Array.from(
      { length },
      (_, index) =>
        new Proxy(
          {
            left: dates[length - index],
            right: dates[length - index - 1],
          },
          {
            ownKeys(target) {
              scans += 1
              return Reflect.ownKeys(target)
            },
          },
        ),
    )
    const result = createPatch({ child: {} }, (draft) => ({
      entries,
      seed: dates[0],
      trigger: draft.child,
    }))
    assert.equal(result.seed, result.entries[length - 1].right)
    for (let index = 1; index < length; index += 1) {
      assert.equal(result.entries[index - 1].right, result.entries[index].left)
    }
    assert.notEqual(result.seed, dates[0])
    // Bound observable graph inspection work rather than machine-dependent elapsed time.
    assert.isBelow(scans, length * 30)
  })
})
