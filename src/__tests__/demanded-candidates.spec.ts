import { assert, it } from 'vitest'

import { reconcile } from '../index'

// When one object of next has several candidates in current, reconcile keeps the one at the first
// position it reads, unless a frozen or getter-only property of an object it keeps requires
// another one there (Spec.Reconcile.demands).

it('keeps the object a frozen property requires, so its owner is kept too', () => {
  const shared = { v: 1 }
  const other = { v: 1 }
  const box = Object.freeze({ item: shared })
  const current = { box, list: [other] }
  const item = { v: 2 }
  reconcile(current, { box: { item }, list: [item] })
  assert.ok(current.list[0] === shared)
  assert.ok(current.box === box)
  assert.equal(shared.v, 2)
})

it('ignores a demand from an object that can never be kept', () => {
  // holder's getter-only property demands that n.a keep target, but n.a is n itself, so holder
  // could only be kept if n kept two objects. The first object read stays.
  const target: Record<string, unknown> = { a: {} }
  const holder = Object.defineProperty({}, 'a', { enumerable: true, get: () => target })
  const keep: Record<string, unknown> = { a: holder }
  const n: Record<string, unknown> = {}
  n.a = n
  const result = reconcile([keep], [n])
  assert.ok(result[0] === keep)
  assert.ok(keep.a === keep)
})
