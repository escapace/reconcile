import { assert, describe, it } from 'vitest'
import { createPatch } from '../index'

describe('buffer clone planning and publication consistency', () => {
  for (const viewFirst of [false, true]) {
    for (const order of [
      ['root', 'box', 'special'],
      ['root', 'special', 'box'],
      ['box', 'root', 'special'],
      ['box', 'special', 'root'],
      ['special', 'root', 'box'],
      ['special', 'box', 'root'],
    ] as const) {
      it(`preserves buffer sharing (view first: ${viewFirst}, order: ${order.join(', ')})`, () => {
        const buffer = new ArrayBuffer(4)
        const typed = new Uint8Array(buffer, 1, 2)
        const view = new DataView(buffer, 1, 2)
        const current = {
          box: { buffer, flag: 0 },
          views: viewFirst ? { ...{ view }, typed } : { typed, view },
        }
        const result = createPatch(current, (draft) => {
          draft.box.flag = 1
          const fields = { box: draft.box, root: draft.views, special: typed }
          return Object.fromEntries(order.map((key) => [key, fields[key]])) as typeof fields
        })
        assert.equal(result.root.typed, result.special)
        assert.equal(result.root.view.buffer, result.special.buffer)
        assert.equal(result.box.buffer, result.special.buffer)
        assert.equal(result.root.view.byteOffset, 1)
        assert.equal(result.root.view.byteLength, 2)
        assert.equal(result.box.flag, 1)
        assert.equal(typed[0], 0)
        result.special[0] = 9
        assert.equal(result.root.view.getUint8(0), 9)
        assert.equal(new Uint8Array(result.box.buffer)[1], 9)
        assert.equal(current.box.flag, 0)
      })
    }
  }
})
