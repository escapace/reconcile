import { assert, it } from 'vitest'

import { produce } from '../index'

it('unwraps replacement getter handles', () => {
  const current = { child: { n: 1 } }
  const result = produce(current, (draft) => ({
    get alias() {
      return draft.child
    },
  }))
  assert.equal(result.alias, current.child)
  assert.equal(Object.getOwnPropertyDescriptor(result, 'alias')?.value, current.child)
})

it('unwraps a later replacement getter after an earlier getter is evaluated', () => {
  const current = { child: { n: 1 } }
  const result = produce(current, (draft) => ({
    get first() {
      return 1
    },
    get second() {
      return draft.child
    },
  }))
  assert.equal(result.second, current.child)
  assert.equal(Object.getOwnPropertyDescriptor(result, 'second')?.value, current.child)
})

it('unwraps getter handles in a recipe-created draft container', () => {
  const current: { child: { n: number }; next?: { alias: { n: number } } } = { child: { n: 1 } }
  const result = produce(current, (draft) => {
    draft.next = {
      get alias() {
        return draft.child
      },
    }
    return draft.next
  })
  assert.equal(result.alias, current.child)
})

it.each([1, 2])('returns false for a rejected equal or changed write of %s', (value) => {
  const current = Object.freeze({ n: 1 })
  const result = produce(current, (draft) => {
    assert.isFalse(Reflect.set(draft, 'n', value))
    return draft
  })
  assert.equal(result, current)
})

it('returns false while retaining partial Reflect.set truncation', () => {
  const current = [0, 1, 2]
  Object.defineProperty(current, '1', { configurable: false })
  const result = produce(current, (draft) => {
    assert.isFalse(Reflect.set(draft, 'length', 0))
    assert.equal(draft.length, 2)
    return draft
  })
  assert.deepEqual(result, [0, 1])
  assert.equal(current.length, 3)
})

it('writes a data property to an explicit receiver', () => {
  const current = { n: 1 }
  const receiver = { n: 0 }
  const result = produce(current, (draft) => {
    assert.isTrue(Reflect.set(draft, 'n', 2, receiver))
    assert.equal(draft.n, 1)
    return draft
  })
  assert.equal(receiver.n, 2)
  assert.equal(result, current)
})

it('invokes an accessor setter with the explicit receiver', () => {
  const current = {
    n: 1,
    get count() {
      return this.n
    },
    set count(value: number) {
      this.n = value
    },
  }
  const receiver = { n: 0 }
  const result = produce(current, (draft) => {
    assert.isTrue(Reflect.set(draft, 'count', 2, receiver))
    return draft
  })
  assert.equal(receiver.n, 2)
  assert.notEqual(result, current)
  assert.deepEqual(result, current)
})

it('tracks an explicit draft receiver without invoking its inherited setter', () => {
  const prototype = {
    get n() {
      return 0
    },
    set n(_value: number) {
      throw new Error('unexpected setter')
    },
  }
  const receiver = Object.create(prototype) as { n: number }
  const current = { receiver, source: { n: 1 } }
  const result = produce(current, (draft) => {
    assert.isTrue(Reflect.set(draft.source, 'n', 2, draft.receiver))
    assert.equal(draft.receiver.n, 2)
    assert.equal(draft.source.n, 1)
    return draft
  })
  assert.equal(result.receiver.n, 2)
  assert.isTrue(Object.hasOwn(result.receiver, 'n'))
  assert.isFalse(Object.hasOwn(current.receiver, 'n'))
})

it('rejects writes to an explicit draft receiver with an own accessor', () => {
  const current = {
    receiver: {
      get n() {
        return 0
      },
    },
    source: { n: 1 },
  }
  const result = produce(current, (draft) => {
    assert.isFalse(Reflect.set(draft.source, 'n', 2, draft.receiver))
    return draft
  })
  assert.notEqual(result, current)
  assert.deepEqual(result, current)
})

it('keeps held recipe state isolated after finalization abandons a throwing getter', () => {
  const failure = new Error('observation failed')
  const current = {
    child: { n: 0 },
    get fail(): never {
      this.child.n = 2
      throw failure
    },
  }
  let held: typeof current | undefined
  assert.throws(
    () =>
      produce(current, (draft) => {
        held = draft
        return draft
      }),
    failure,
  )
  assert(held !== undefined)
  assert.equal(current.child.n, 0)
  assert.equal(held.child.n, 2)
  held.child.n = 3
  assert.equal(current.child.n, 0)
  const next = produce(current, (draft) => ({ child: draft.child }))
  assert.equal(next.child, current.child)
  assert.equal(next.child.n, 0)
  assert.equal(held.child.n, 3)
})

it.each([1, 2])('keeps reentrant array writes when length coercion %s throws', (throwAt) => {
  const current = [0, 1, 2]
  const failure = new Error('coercion failed')
  const result = produce(current, (draft) => {
    let calls = 0
    const length = {
      valueOf() {
        calls += 1
        draft[4] = 9
        if (calls === throwAt) throw failure
        return 0
      },
    }
    assert.throws(() => Reflect.set(draft, 'length', length), failure)
    assert.equal(calls, throwAt)
    assert.equal(draft.length, 5)
    assert.equal(draft[2], 2)
    return draft
  })
  assert.equal(result.length, 5)
  assert.equal(result[4], 9)
  assert.isFalse(3 in result)
  assert.deepEqual(current, [0, 1, 2])
})
