import { assert, it } from 'vitest'

import { isReconcileError, isReconcileErrorOfType, produce, reconcile, snapshot } from '../index'

it.each(['__v_raw', '__v_isReactive', '__v_isReadonly'] as const)(
  'does not invoke an inherited application getter for %s while resolving storage',
  (marker) => {
    const raw = { n: 0 }
    const prototype = { __v_isReactive: false, __v_isReadonly: false, __v_raw: raw }
    let reads = 0
    Object.defineProperty(prototype, marker, {
      get() {
        reads += 1
        throw new Error('Application marker getter was invoked')
      },
    })
    const candidate = Object.assign(Object.create(prototype) as { n: number }, { n: 0 })
    const current = { left: raw, right: candidate }
    assert.equal(reconcile(current, { left: { n: 1 }, right: { n: 2 } }), current)
    assert.equal(reads, 0)
    assert.equal(current.left, raw)
    assert.equal(current.right, candidate)
    assert.equal(raw.n, 1)
    assert.equal(candidate.n, 2)
  },
)

it('does not treat a raw marker with disabled wrapper flags as shared storage', () => {
  const raw = { n: 0 }
  const candidate = Object.assign(
    Object.create({
      __v_isReactive: false,
      __v_isReadonly: false,
      __v_raw: raw,
    }) as { n: number },
    { n: 0 },
  )
  const current = { left: raw, right: candidate }
  const next = produce(current, (draft) => {
    draft.left.n = 1
    draft.left.n = 0
    draft.right.n = 1
    draft.right.n = 0
    return draft
  })
  assert.equal(next, current)
  assert.equal(next.left, raw)
  assert.equal(next.right, candidate)
  next.left.n = 3
  assert.equal(next.right.n, 0)
})

it('terminates cyclic raw-marker chains without merging independent identities', () => {
  const left = { n: 0 }
  const right = { n: 0 }
  Object.setPrototypeOf(left, { __v_isReactive: true, __v_raw: right })
  Object.setPrototypeOf(right, { __v_isReadonly: true, __v_raw: left })
  const current = { left, right }
  assert.equal(reconcile(current, { left: { n: 1 }, right: { n: 2 } }), current)
  assert.equal(current.left, left)
  assert.equal(current.right, right)
  assert.equal(left.n, 1)
  assert.equal(right.n, 2)
  left.n = 9
  assert.equal(right.n, 2)
})

const rejected = (run: () => unknown): void => {
  try {
    run()
  } catch (error) {
    assert.ok(isReconcileError(error) && isReconcileErrorOfType(error, 'PublicationRejected'))
    return
  }
  assert.fail('expected the publication to be rejected')
}

it('rejects a fresh target whose wrapper markers resolve to old storage', () => {
  const old = { n: 0 }
  const fresh = Object.assign(
    Object.create({ __v_isReactive: true, __v_raw: old }) as { n: number },
    { n: 1 },
  )
  const current: { a: object; list: object[] } = { a: old, list: [] }
  rejected(() => reconcile(current, { a: { n: 0 }, list: [fresh] }))
  assert.equal(current.a, old)
})

it('rejects two fresh targets whose wrapper markers resolve to one storage', () => {
  const shared = { n: 0 }
  const next = {
    a: { n: 9 },
    x: Object.assign(Object.create({ __v_isReactive: true, __v_raw: shared }) as object, { n: 1 }),
    y: Object.assign(Object.create({ __v_isReadonly: true, __v_raw: shared }) as object, { n: 2 }),
  }
  rejected(() => reconcile({ a: { n: 9 } }, next))
})

// A Map or Set is asked whether it is a Vue wrapper with fewer reads than an ordinary object, and
// still never through an application getter of a marker.
it.each(['map', 'set'] as const)(
  'does not invoke an inherited marker getter of a %s in any function',
  (kind) => {
    let reads = 0
    const define = (prototype: object) =>
      Object.defineProperty(prototype, '__v_raw', {
        get() {
          reads += 1
          throw new Error('Application marker getter was invoked')
        },
      })
    class Marked extends Map<unknown, unknown> {}
    class Members extends Set<unknown> {}
    define(Marked.prototype)
    define(Members.prototype)
    const make = (value: number) =>
      kind === 'map' ? new Marked([['a', { value }]]) : new Members([value, { value }])
    const current = { collection: make(1) }
    const kept = current.collection
    const copy = snapshot(current) as typeof current
    reconcile(current, { collection: make(2) })
    const result = produce(current, (draft) => {
      const collection = draft.collection as Map<unknown, unknown> & Set<unknown>
      if (kind === 'map') collection.set('b', 3)
      else collection.add(3)
      return draft
    })
    assert.equal(reads, 0)
    assert.equal(current.collection, kept)
    assert.notEqual(copy.collection, kept)
    assert.equal(result.collection.size, kind === 'map' ? 2 : 3)
  },
)
