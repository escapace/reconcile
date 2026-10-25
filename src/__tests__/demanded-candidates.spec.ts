/* eslint-disable perfectionist/sort-objects -- Key order is the visit order these cases depend on. */
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

const fixed = <T extends object>(o: T, key: string, value: unknown): T =>
  Object.defineProperty(o, key, { configurable: false, enumerable: true, value, writable: false })

it('ignores a demand from an object whose fixed slots require two objects at one node', () => {
  // holder could be kept at n.c only if n.o kept both first and second.
  const first = {}
  const second = {}
  const kept = {}
  const holder = fixed(fixed({}, 'a', first), 'b', second)
  const current = { o: kept, c: holder }
  const shared = { x: 1 }
  const result = reconcile(current, { o: shared, c: { a: shared, b: shared } })
  assert.ok(result.o === kept)
  assert.ok(result.c !== holder)
})

it('ignores a demand from an object whose fixed slot requires another object at a pinned node', () => {
  // place stays in place, so holder, which holds a copy of it, can never be kept at n.c. Capture
  // meets place first at a, before the object that keeps it in place, or only inside that object;
  // the first object read stays either way.
  for (const early of [false, true]) {
    const place = { p: 1 }
    const kept = {}
    const holder = fixed(fixed({}, 'f', { p: 1 }), 'k', {})
    const box = { in: place }
    const current = { a: early ? { p: 0 } : box, o: kept, q: box, c: holder }
    const shared = { x: 1 }
    const result = reconcile(current, {
      a: early ? place : box,
      o: shared,
      q: box,
      c: { f: place, k: shared },
    })
    assert.ok(result.o === kept)
    assert.ok(result.q === box && box.in === place)
  }
})
