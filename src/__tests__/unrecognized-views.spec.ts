// A view over a buffer this environment does not recognize is not recognized either: every
// function handles it as a class instance, whichever of the view and its buffer comes first.
import { runInNewContext } from 'node:vm'
import { expect, it } from 'vitest'
import { isReconcileErrorOfType, produce, reconcile, serialize, snapshot } from '../index'

/** A view over a buffer whose prototype was replaced, and one from another environment. */
const views = (): Uint8Array[] => {
  const replaced = new Uint8Array([1, 2])
  Object.setPrototypeOf(replaced.buffer, null)
  return [replaced, runInNewContext('new Uint8Array([3, 4])') as Uint8Array]
}

/** A class instance copy of a two-element view: its elements as own data properties. */
const expectInstanceCopy = (copy: unknown, view: Uint8Array): void => {
  expect(ArrayBuffer.isView(copy)).toBe(false)
  expect(Object.getPrototypeOf(copy)).toBe(Object.getPrototypeOf(view))
  expect(Object.getOwnPropertyNames(copy)).toEqual(['0', '1'])
  expect([(copy as Uint8Array)[0], (copy as Uint8Array)[1]]).toEqual([view[0], view[1]])
}

it('copies such a view as a class instance whether its buffer comes first or not', () => {
  for (const view of views()) {
    const [, after] = snapshot([view.buffer, view]) as unknown[]
    const [before] = snapshot([view, view.buffer]) as unknown[]
    expectInstanceCopy(after, view)
    expectInstanceCopy(before, view)
  }
})

it('lets reconcile and produce place such a view as a class instance', () => {
  for (const view of views()) {
    expectInstanceCopy((reconcile({}, { view }) as { view: unknown }).view, view)
    const next = produce({ view }, (draft) => {
      draft.view[0] = 9
      return draft
    })
    expect(ArrayBuffer.isView(next.view)).toBe(false)
    expect(next.view[0]).toBe(9)
  }
})

it('rejects in serialize a view over a buffer without the standard prototype', () => {
  for (const prototype of [null, Object.prototype]) {
    const view = new Uint8Array(2)
    Object.setPrototypeOf(view.buffer, prototype)
    for (const value of [view, [view.buffer, view]]) {
      let thrown: unknown
      try {
        serialize(value)
      } catch (error) {
        thrown = error
      }
      expect(isReconcileErrorOfType(thrown as never, 'SerializeValueUnsupported')).toBe(true)
    }
  }
})
