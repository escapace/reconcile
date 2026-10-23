import { assert, it } from 'vitest'
import { produce, reconcile, snapshot } from '../index'

it('writes a date only when its time changes, without calling overrides', () => {
  let calls = 0
  class Tracked extends Date {
    override getTime(): number {
      calls += 1
      return super.getTime() + 1
    }

    override setTime(time: number): number {
      calls += 1
      return super.setTime(time)
    }
  }
  const state = { changed: new Tracked(0), same: new Tracked(0) }
  reconcile(state, { changed: new Date(5), same: new Date(0) })
  assert.equal(calls, 0)
  assert.equal(Date.prototype.getTime.call(state.changed), 5)
  assert.equal(Date.prototype.getTime.call(state.same), 0)
})

it('copies and compares a date by its built-in time', () => {
  class Shifted extends Date {
    override getTime(): number {
      return super.getTime() + 3_600_000
    }
  }
  const value = new Shifted(0)
  const copy = snapshot(value) as Date
  assert.ok(copy instanceof Shifted)
  assert.equal(Date.prototype.getTime.call(copy), 0)
  const result = produce({ value }, (draft) => {
    void draft.value
    return draft
  })
  assert.strictEqual(result.value, value)
})
