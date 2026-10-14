import { assert, it } from 'vitest'

import { produce, ReconcileError } from '../index'

it('honors an explicit external receiver after that object has acquired a draft handle', () => {
  const external = { value: 0 }
  const current: { source: { value: number }; receiver?: { value: number } } = {
    source: { value: 1 },
  }
  const result = produce(current, (draft) => {
    draft.receiver = external
    const handle = draft.receiver
    assert.notEqual(handle, external)
    assert.isTrue(Reflect.set(draft.source, 'value', 2, external))
    assert.equal(external.value, 2)
    assert.equal(handle.value, 2)
    return draft
  })
  assert.equal(result.receiver, external)
  assert.equal(result.source, current.source)
  assert.equal(current.source.value, 1)
})

function accessorArray() {
  const current = [{ n: 0 }, { n: 1 }]
  Object.defineProperty(current, '0', {
    configurable: true,
    enumerable: true,
    get(this: Array<{ n: number }>) {
      return this[1]
    },
    set(this: Array<{ n: number }>, value: { n: number }) {
      this[1] = value
    },
  })
  return current
}

it('preserves indexed getters after replacing their backing element', () => {
  const current = accessorArray()
  const result = produce(current, (draft) => {
    const held = draft[0]
    draft[1] = { n: 2 }
    assert.equal(draft[0], draft[1])
    assert.notEqual(draft[0], held)
    draft[0].n = 3
    return draft
  })
  assert.equal(result[0], result[1])
  assert.equal(result[1].n, 3)
  assert.equal(current[1].n, 1)
})

it('preserves indexed setters after an unrelated array mutation', () => {
  const current = accessorArray()
  const result = produce(current, (draft) => {
    draft.push({ n: 4 })
    draft[0] = { n: 2 }
    assert.equal(draft[1].n, 2)
    return draft
  })
  assert.equal(result[0], result[1])
  assert.deepEqual(
    result.map((value) => value.n),
    [2, 2, 4],
  )
  assert.equal(current.length, 2)
  assert.equal(current[1].n, 1)
})

it('finalizes indexed getters against nested draft changes', () => {
  const current: Array<number | { n: number }> = [0, { n: 1 }]
  Object.defineProperty(current, '0', {
    configurable: true,
    enumerable: true,
    get(this: typeof current) {
      return (this[1] as { n: number }).n
    },
  })
  const result = produce(current, (draft) => {
    ;(draft[1] as { n: number }).n = 2
    return draft
  })
  assert.equal(result[0], 2)
  assert.equal(current[0], 1)
})

it.each([false, true])('rejects property definitions on drafts with array = %s', (array) => {
  const current = array ? [1] : { value: 1 }
  const key = array ? '0' : 'value'
  const result = produce(current, (draft) => {
    const descriptor = { configurable: true, value: 2, writable: true }
    assert.throws(
      () => Reflect.defineProperty(draft, key, descriptor),
      ReconcileError,
      /use assignment instead/,
    )
    assert.throws(
      () => Object.defineProperty(draft, key, descriptor),
      ReconcileError,
      /use assignment instead/,
    )
    return draft
  })
  assert.equal(result, current)
  assert.equal(Reflect.get(current, key), 1)
})

it.each([null, 7, { n: 1 }])('publishes an own __proto__ accessor value %s', (value) => {
  const current = { touched: 0 }
  Object.defineProperty(current, '__proto__', {
    configurable: true,
    enumerable: true,
    get() {
      return value
    },
  })
  const result = produce(current, (draft) => {
    draft.touched = 1
    return draft
  })
  assert.deepEqual(Reflect.ownKeys(result), ['touched', '__proto__'])
  assert.equal(Object.getPrototypeOf(result), Object.getPrototypeOf(current))
  assert.deepEqual(Object.getOwnPropertyDescriptor(result, '__proto__')?.value, value)
  assert.equal(current.touched, 0)
})
