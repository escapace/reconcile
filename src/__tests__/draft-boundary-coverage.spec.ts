import { assert, it } from 'vitest'

import { produce, snapshot } from '../index'

it.each([-1, 1.5, Number.NaN, Number.POSITIVE_INFINITY, 2 ** 32])(
  'rejects invalid array length %s without losing earlier isolated edits',
  (length) => {
    const current = [0, 1]
    const next = produce(current, (draft) => {
      draft[0] = 2
      assert.throws(() => Reflect.set(draft, 'length', length), RangeError)
      assert.equal(draft.length, 2)
      assert.deepEqual([...draft], [2, 1])
      return draft
    })
    assert.deepEqual(next, [2, 1])
    assert.deepEqual(current, [0, 1])
  },
)

it('rejects inconsistent two-step array length coercion without truncating the draft', () => {
  const current = [0, 1, 2]
  let coercions = 0
  const next = produce(current, (draft) => {
    assert.throws(
      () =>
        Reflect.set(draft, 'length', {
          valueOf() {
            coercions += 1
            return coercions === 1 ? 1 : 2
          },
        }),
      RangeError,
    )
    assert.equal(coercions, 2)
    assert.deepEqual([...draft], [0, 1, 2])
    return draft
  })
  assert.equal(next, current)
})

it('rejects index growth at a readonly length while allowing an existing element edit', () => {
  const current = [0]
  Object.defineProperty(current, 'length', { writable: false })
  const next = produce(current, (draft) => {
    assert.isFalse(Reflect.set(draft, '1', 2))
    assert.isFalse(1 in draft)
    assert.equal(draft.length, 1)
    draft[0] = 3
    return draft
  })
  assert.deepEqual(next, [3])
  assert.deepEqual(current, [0])
  assert.isFalse(Object.getOwnPropertyDescriptor(current, 'length')!.writable)
})

it('reflects an accessor without invoking it and rejects assignment without a setter', () => {
  let reads = 0
  const getter = () => {
    reads += 1
    return 2
  }
  const current: { n: number; computed?: number } = { n: 0 }
  Object.defineProperty(current, 'computed', { configurable: true, enumerable: true, get: getter })
  const next = produce(current, (draft) => {
    const descriptor = Object.getOwnPropertyDescriptor(draft, 'computed')!
    assert.deepEqual(descriptor, {
      configurable: true,
      enumerable: true,
      get: getter,
      set: undefined,
    })
    assert.equal(reads, 0)
    assert.isFalse(Reflect.set(draft, 'computed', 9))
    assert.equal(reads, 0)
    draft.n = 1
    return draft
  })
  assert.equal(reads, 1)
  assert.deepEqual(next, { computed: 2, n: 1 })
  assert.equal(current.n, 0)
  assert.deepEqual(Object.getOwnPropertyDescriptor(current, 'computed'), {
    configurable: true,
    enumerable: true,
    get: getter,
    set: undefined,
  })
})

it('reads missing copied properties on a null prototype and rejects primitive receivers', () => {
  const current = Object.assign(Object.create(null) as Record<string, unknown>, { n: 0 })
  const next = produce(current, (draft) => {
    draft.n = 1
    assert.isUndefined(draft.missing)
    assert.isFalse('missing' in draft)
    assert.isFalse(Reflect.set(draft, 'n', 9, 42))
    assert.equal(draft.n, 1)
    return draft
  })
  assert.isNull(Object.getPrototypeOf(next))
  assert.equal(next.n, 1)
  assert.equal(current.n, 0)
})

it('restores sparse array identity after an edit is undone without filling holes', () => {
  const current = new Array<number>(3)
  current[2] = 2
  const next = produce(current, (draft) => {
    draft[2] = 3
    draft[2] = 2
    return draft
  })
  assert.equal(next, current)
  assert.isFalse(0 in next)
  assert.isFalse(1 in next)
  assert.equal(next[2], 2)
})

it('does not restore a base when deletion and reinsertion change only key order', () => {
  const child = { n: 0 }
  const current: { second: number; first?: typeof child } = { first: child, second: 2 }
  const next = produce(current, (draft) => {
    const held = draft.first
    delete draft.first
    draft.first = held
    return draft
  })
  assert.notEqual(next, current)
  assert.deepEqual(Reflect.ownKeys(next), ['second', 'first'])
  assert.deepEqual(Reflect.ownKeys(current), ['first', 'second'])
  assert.equal(next.first, child)
  const detached = snapshot(next) as typeof next
  assert.deepEqual(Reflect.ownKeys(detached), ['second', 'first'])
  assert.notEqual(detached.first, child)
  detached.first!.n = 7
  assert.equal(child.n, 0)
})

it('keeps detachment of a writable buffer copy isolated from the original', () => {
  const current = new Uint8Array([1, 2, 3, 4]).buffer
  let transferred: ArrayBuffer | undefined
  const next = produce(current, (draft) => {
    transferred = structuredClone(draft, { transfer: [draft] })
    assert.equal(draft.byteLength, 0)
    return draft
  })
  assert.notEqual(next, current)
  assert.equal(next.byteLength, 0)
  assert.throws(() => new Uint8Array(next), TypeError)
  assert.deepEqual([...new Uint8Array(current)], [1, 2, 3, 4])
  assert.deepEqual([...new Uint8Array(transferred!)], [1, 2, 3, 4])
})

it('does not restore a typed view whose writable backing buffer was detached', () => {
  const current = new Uint8Array([1, 2, 3, 4])
  const next = produce(current, (draft) => {
    structuredClone(draft.buffer, { transfer: [draft.buffer] })
    return draft
  })
  assert.notEqual(next, current)
  assert.equal(next.byteLength, 0)
  assert.throws(() => new Uint8Array(next.buffer), TypeError)
  assert.deepEqual([...current], [1, 2, 3, 4])
})
