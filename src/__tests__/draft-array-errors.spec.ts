import { assert, it } from 'vitest'

import { isReconcileError, produce } from '../index'

// An array proxy whose own keys and descriptors no real array could have: each documented draft
// array error names the impossible fact. The proxy must respect its target's invariants, so the
// target carries the non-configurable facts the proxy reports.

const extra = { configurable: true, enumerable: true, value: 'x', writable: true }

/** The `cause` of the error that a write into a draft of `{ array }` throws. */
function causeOf(array: unknown[]): unknown {
  try {
    produce({ array }, (draft) => {
      draft.array[0] = 'written'
    })
  } catch (error) {
    if (isReconcileError(error)) return error.cause
    throw error
  }
  return undefined
}

it('rejects an index at or beyond a non-writable length', () => {
  const target: unknown[] = [1]
  Object.defineProperty(target, 'length', { writable: false })
  const array = new Proxy(target, {
    get: (t, key, receiver) =>
      key === '5' ? extra.value : (Reflect.get(t, key, receiver) as unknown),
    getOwnPropertyDescriptor: (t, key) =>
      key === '5' ? extra : Reflect.getOwnPropertyDescriptor(t, key),
    // The length comes first, so its non-writable attribute is known when the index arrives.
    ownKeys: () => ['length', '0', '5'],
  })
  assert.deepEqual(causeOf(array), { index: 5, type: 'DraftArrayIndexRejected' })
})

it('rejects a length below a non-configurable index', () => {
  const target: unknown[] = [1, 2, 3, 4, 5, 6]
  Object.defineProperty(target, 5, { configurable: false })
  const length = { configurable: false, enumerable: false, value: 2, writable: true }
  const array = new Proxy(target, {
    get: (t, key, receiver) =>
      key === 'length' ? length.value : (Reflect.get(t, key, receiver) as unknown),
    getOwnPropertyDescriptor: (t, key) =>
      key === 'length' ? length : Reflect.getOwnPropertyDescriptor(t, key),
  })
  assert.deepEqual(causeOf(array), { length: 2, type: 'DraftArrayLengthRejected' })
})
