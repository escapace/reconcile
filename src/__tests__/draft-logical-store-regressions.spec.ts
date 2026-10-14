import { assert, it } from 'vitest'

import { produce } from '../index'

it('keeps held draft handles independent from the published graph in both directions', () => {
  const current = { child: { value: 0 }, count: 0 }
  let held!: typeof current
  let child!: typeof current.child
  const next = produce(current, (draft) => {
    held = draft
    child = draft.child
    draft.count = 1
    child.value = 2
    return draft
  })

  assert.equal(held.child, child)
  assert.equal(held.child.value, 2)
  next.child.value = 3
  next.count = 4
  assert.equal(held.child, child)
  assert.equal(held.child.value, 2)
  assert.equal(held.count, 1)
  held.child.value = 5
  held.count = 6
  assert.deepEqual(next, { child: { value: 3 }, count: 4 })
  assert.deepEqual(current, { child: { value: 0 }, count: 0 })
})

it('copies public reflection descriptors without changing draft writability or child handles', () => {
  const current = { child: { value: 0 }, count: 0, fixed: 1 }
  Object.defineProperty(current, 'fixed', { configurable: false, writable: false })
  const next = produce(current, (draft) => {
    draft.count = 1
    const child = draft.child
    const descriptor = Object.getOwnPropertyDescriptor(draft, 'child')!
    assert.equal(descriptor.value, child)
    descriptor.value = { value: 100 }
    descriptor.writable = false
    const fixed = Object.getOwnPropertyDescriptor(draft, 'fixed')!
    assert.isTrue(fixed.configurable)
    assert.isFalse(Reflect.deleteProperty(draft, 'fixed'))
    assert.isFalse(Reflect.set(draft, 'fixed', 2))
    assert.equal(draft.child, child)
    draft.child = { value: 2 }
    return draft
  })
  assert.equal(next.child.value, 2)
  assert.equal(next.fixed, 1)
  assert.deepEqual(current, { child: { value: 0 }, count: 0, fixed: 1 })
})

it('keeps the eager first-write observation boundary for subsequent draft reads', () => {
  let exposed = 0
  const reads: PropertyKey[] = []
  const current = new Proxy(
    { a: 0, b: 0 },
    {
      get(target, key, receiver) {
        if (key === 'b') {
          reads.push(key)
          return exposed
        }
        return Reflect.get(target, key, receiver) as unknown
      },
    },
  )
  produce(current, (draft) => {
    draft.a = 1
    assert.deepEqual(reads, ['b'])
    exposed = 2
    assert.equal(draft.b, 0)
    return draft
  })
  assert.equal(current.a, 0)
})

it('matches partial native truncation when length coercion itself grows the array', () => {
  const current = [1, 2, 3]
  Object.defineProperty(current, '1', { configurable: false })
  const next = produce(current, (draft) => {
    let coercions = 0
    const success = Reflect.set(draft, 'length', {
      valueOf() {
        coercions += 1
        draft[3] = 4
        return 0
      },
    })
    assert.isFalse(success)
    assert.equal(coercions, 2)
    assert.equal(draft.length, 2)
    assert.isFalse(2 in draft)
    assert.isFalse(3 in draft)
    return draft
  })
  assert.deepEqual(next, [1, 2])
  assert.deepEqual(current, [1, 2, 3])
})

it('observes a copied property introduced during an inherited presence check', () => {
  interface Value {
    count: number
    late?: { value: number }
  }
  let held!: Value
  let checks = 0
  const prototype = new Proxy(
    {},
    {
      has(target, key) {
        if (key === 'late') {
          checks += 1
          held.late = { value: 2 }
          return true
        }
        return Reflect.has(target, key)
      },
    },
  )
  const current = Object.assign(Object.create(prototype) as Value, { count: 0 })
  const next = produce(current, (draft) => {
    held = draft
    draft.count = 1
    assert.equal(draft.late?.value, 2)
    assert.equal(draft.late?.value, 2)
    assert.equal(checks, 1)
    return draft
  })
  assert.equal(next.late?.value, 2)
  assert.isFalse(Object.hasOwn(current, 'late'))
  assert.equal(current.count, 0)
})
