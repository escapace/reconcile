import { assert, it } from 'vitest'

import { produce, ReconcileError } from '../index'

it('rejects a new accessor introduced behind an already captured edge instead of observing it after sealing', () => {
  const child = { value: 0 }
  const current = { child, flag: 0 }
  let replacements = 0
  let lateReads = 0
  Object.defineProperty(current, 'replace', {
    configurable: true,
    enumerable: true,
    get(this: typeof current) {
      replacements += 1
      this.child = {
        get value() {
          lateReads += 1
          return 2
        },
      }
      return 1
    },
  })

  assert.throws(
    () =>
      produce(current, (draft) => {
        draft.flag = 1
        return draft
      }),
    ReconcileError,
    'Finalization accessor "value" appeared after sealing.',
  )
  assert.equal(replacements, 1)
  assert.equal(lateReads, 0)
  assert.equal(current.child, child)
  assert.equal(child.value, 0)
  assert.equal(current.flag, 0)
})
