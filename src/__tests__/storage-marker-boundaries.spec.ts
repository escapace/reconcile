import { assert, it } from 'vitest'
import { reactive, readonly } from 'vue'

import { isReconcileError, isReconcileErrorOfType, produce, reconcile, snapshot } from '../index'

it('reads __v_raw with one [[Get]], running an application getter of that name', () => {
  const raw = { n: 0 }
  let reads = 0
  const prototype = { __v_isReactive: false, __v_isReadonly: false }
  const failures: Error[] = []
  Object.defineProperty(prototype, '__v_raw', {
    get() {
      reads += 1
      if (failures.length !== 0) throw failures[0]
      return raw
    },
  })
  const candidate = Object.assign(Object.create(prototype) as { n: number }, { n: 0 })
  const current = { left: raw, right: candidate }
  assert.equal(reconcile(current, { left: { n: 1 }, right: { n: 2 } }), current)
  assert.isAbove(reads, 0)
  // Without Vue's flags the object the getter returns is not candidate's storage.
  assert.equal(current.left, raw)
  assert.equal(current.right, candidate)
  assert.equal(raw.n, 1)
  assert.equal(candidate.n, 2)
  // An error the getter throws propagates unchanged.
  failures.push(new Error('marker'))
  assert.throws(() => snapshot(current), failures[0])
})

it.each(['__v_isReactive', '__v_isReadonly'] as const)(
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

it('captures two wrappers of one raw object in next as one object', () => {
  const raw = { n: 1 }
  const next = { a: { n: 9 }, x: reactive(raw), y: readonly(raw) }
  const current: Record<string, unknown> = { a: { n: 9 } }
  reconcile(current, next)
  // A Vue proxy is a view of its raw object: `current` holds one object at both positions.
  assert.strictEqual(current.x, current.y)
  assert.deepEqual(current.x, { n: 1 })
})

// A Map or Set is asked whether it is a Vue wrapper by the same one read as an ordinary object.
it.each(['map', 'set'] as const)(
  'treats a %s with an inherited marker getter that returns no object as ordinary',
  (kind) => {
    let reads = 0
    const define = (prototype: object) =>
      Object.defineProperty(prototype, '__v_raw', {
        get() {
          reads += 1
          return undefined
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
    assert.isAbove(reads, 0)
    assert.equal(current.collection, kept)
    assert.notEqual(copy.collection, kept)
    assert.equal(result.collection.size, kind === 'map' ? 2 : 3)
  },
)
