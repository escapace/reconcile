/**
 * `current` and `next` sharing objects at different positions.
 *
 * BUG: reconcile's in-place writes cascaded through the shared references, corrupting data, and
 * changed `next`.
 *
 * FIX: reconcile never writes into an object that `next` holds. Each shape below holds objects of
 * `current` at other positions of `next`, so reconcile throws `PublicationWouldChangeNext` before
 * any write and changes neither argument. Matching a detached copy of `next` by index, ordinal or
 * key is covered by `reconcile-semantics.spec.ts`.
 */

import { assert, describe, it } from 'vitest'
import { produce, reconcile, snapshot } from '../index'
import { assertWouldChangeNext } from './fixtures/graph-state'

/** `current`, and a `next` that holds objects of `current` at other positions. */
type Shape = () => readonly [current: object, next: object]

/** A `Set` with the members of `set` in `order`, made by a recipe as an application would. */
const reorderSet = <T>(set: Set<T>, order: readonly T[]): Set<T> =>
  produce(set, (draft) => {
    draft.clear()
    for (const member of order) draft.add(member)
    return draft
  })

const SHAPES: ReadonlyArray<readonly [name: string, shape: Shape]> = [
  [
    'a reordered Set',
    () => {
      const [a, b, c] = [{ id: 'a' }, { id: 'b' }, { id: 'c' }]
      const current = new Set([a, b, c])
      return [current, reorderSet(current, [c, a, b])]
    },
  ],
  [
    'two swapped Set members',
    () => {
      const [x, y] = [{ name: 'x' }, { name: 'y' }]
      const current = new Set([x, y])
      return [current, reorderSet(current, [y, x])]
    },
  ],
  [
    'a rotated Set',
    () => {
      const items = [{ n: 1 }, { n: 2 }, { n: 3 }, { n: 4 }]
      const current = new Set(items)
      return [current, reorderSet(current, [items[1], items[2], items[3], items[0]])]
    },
  ],
  [
    'a Map with reordered entries',
    () => {
      const [k1, k2, v1, v2] = [{ key: 'k1' }, { key: 'k2' }, { val: 'v1' }, { val: 'v2' }]
      const current = new Map([
        [k1, v1],
        [k2, v2],
      ])
      const next = produce(current, (draft) => {
        draft.clear()
        draft.set(k2, v2)
        draft.set(k1, v1)
        return draft
      })
      return [current, next]
    },
  ],
  [
    'a Map with swapped values',
    () => {
      const [v1, v2] = [{ data: 'first' }, { data: 'second' }]
      const current = new Map([
        ['a', v1],
        ['b', v2],
      ])
      const next = produce(current, (draft) => {
        draft.set('a', v2)
        draft.set('b', v1)
        return draft
      })
      return [current, next]
    },
  ],
  [
    'a Map with swapped keys',
    () => {
      const [k1, k2] = [{ id: 1 }, { id: 2 }]
      const current = new Map([
        [k1, 'first'],
        [k2, 'second'],
      ])
      const next = produce(current, (draft) => {
        draft.clear()
        draft.set(k2, 'first')
        draft.set(k1, 'second')
        return draft
      })
      return [current, next]
    },
  ],
  [
    'a Map built with its keys reordered',
    () => {
      const [k1, k2] = [{ id: 'k1' }, { id: 'k2' }]
      const current = new Map([
        [k1, 1],
        [k2, 2],
      ])
      /* eslint-disable perfectionist/sort-maps */
      const next = new Map([
        [k2, 2],
        [k1, 1],
      ])
      /* eslint-enable perfectionist/sort-maps */
      return [current, next]
    },
  ],
  [
    'a reordered array',
    () => {
      const [a, b, c] = [{ id: 'a' }, { id: 'b' }, { id: 'c' }]
      return [
        [a, b, c],
        [c, a, b],
      ]
    },
  ],
  [
    'two swapped array elements',
    () => {
      const [x, y] = [{ value: 10 }, { value: 20 }]
      return [
        [x, y],
        [y, x],
      ]
    },
  ],
  [
    'a reversed array',
    () => {
      const items = [{ n: 1 }, { n: 2 }, { n: 3 }]
      return [items, [...items].reverse()]
    },
  ],
  [
    'an array rotated with pop and unshift',
    () => {
      const current = [{ letter: 'a' }, { letter: 'b' }, { letter: 'c' }]
      const next = produce(current, (draft) => {
        draft.unshift(draft.pop()!)
        return draft
      })
      return [current, next]
    },
  ],
  [
    'swapped property values',
    () => {
      const [x, y] = [{ name: 'x' }, { name: 'y' }]
      return [
        { first: x, second: y },
        { first: y, second: x },
      ]
    },
  ],
  [
    'rotated property values',
    () => {
      const [a, b, c] = [{ v: 'a' }, { v: 'b' }, { v: 'c' }]
      return [
        { p1: a, p2: b, p3: c },
        { p1: b, p2: c, p3: a },
      ]
    },
  ],
  [
    'swapped property values in a new key order',
    () => {
      const [x, y] = [{ id: 'x' }, { id: 'y' }]
      return [
        { a: x, b: y },
        // eslint-disable-next-line perfectionist/sort-objects -- next reverses the key order.
        { b: x, a: y },
      ]
    },
  ],
  [
    'swapped wrappers around one shared object',
    () => {
      const shared = { count: 0 }
      const wrapper1 = { id: 'w1', inner: shared }
      const wrapper2 = { id: 'w2', inner: shared }
      return [
        { a: wrapper1, b: wrapper2 },
        { a: wrapper2, b: wrapper1 },
      ]
    },
  ],
  [
    'objects swapped in an array and an object at once',
    () => {
      const [a, b] = [{ id: 'a' }, { id: 'b' }]
      return [
        { array: [a, b], obj: { x: a, y: b } },
        { array: [b, a], obj: { x: b, y: a } },
      ]
    },
  ],
  [
    'a reorder deep inside nested objects',
    () => {
      const a = { deep: { value: 'a' } }
      const b = { deep: { value: 'b' } }
      return [{ level1: { level2: { items: [a, b] } } }, { level1: { level2: { items: [b, a] } } }]
    },
  ],
  [
    'swapped members of a cycle',
    () => {
      const a: { id: string; next?: object } = { id: 'a' }
      const b: { id: string; next?: object } = { id: 'b' }
      a.next = b
      b.next = a
      return [
        { first: a, second: b },
        { first: b, second: a },
      ]
    },
  ],
]

describe('reconcile with next holding objects of current at other positions', () => {
  for (const [name, shape] of SHAPES)
    it(`throws for ${name} and changes neither argument`, () => {
      const [current, next] = shape()
      assertWouldChangeNext(current, next)
    })

  it('rebuilds nested reordered objects from a detached next without re-planning children', () => {
    const xa = { id: 'xa' }
    const xb = { id: 'xb' }
    const yc = { id: 'yc' }
    const yd = { id: 'yd' }
    const x = { a: xa, b: xb }
    // eslint-disable-next-line perfectionist/sort-objects
    const y = { b: yc, a: yd }
    const current = { left: x, right: y }
    const next = { left: y, right: x }
    assertWouldChangeNext(current, next)
    const result = reconcile(current, snapshot(next) as typeof next)
    assert.equal(result, current)
    assert.equal(result.left, x)
    assert.equal(result.right, y)
    assert.deepEqual(Object.keys(result.left), ['b', 'a'])
    assert.deepEqual(Object.keys(result.right), ['a', 'b'])
    assert.equal(result.left.b.id, 'yc')
    assert.equal(result.left.a.id, 'yd')
    assert.equal(result.right.a.id, 'xa')
    assert.equal(result.right.b.id, 'xb')
  })

  it('keeps an object in place when current holds it twice and next reorders around it', () => {
    const a = { id: 'a' }
    const b = { id: 'b' }
    const original = [a, a, b]
    const result = reconcile(
      original,
      produce(original, (draft) => {
        draft[0] = b
        draft[1] = a
        draft[2] = a
        return draft
      }),
    )
    assert.deepEqual(
      result.map((x) => x.id),
      ['b', 'a', 'a'],
    )
  })
})

describe('produce produces shared identities - reconcile handles correctly', () => {
  it('produce output shares identities with current', () => {
    const a = { id: 'a' }
    const b = { id: 'b' }
    const current = new Set([a, b])
    const next = reorderSet(current, [b, a])
    // next contains the same objects as current
    const nextArray = [...next]
    assert.equal(nextArray[0], b, 'next[0] should be b (same identity)')
    assert.equal(nextArray[1], a, 'next[1] should be a (same identity)')
    // reconcile would write into a and b, which next holds: it throws and changes neither.
    assertWouldChangeNext(current, next)
    // After reconciling a detached copy of next, values are swapped
    const result = reconcile(current, snapshot(next) as typeof next)
    assert.equal(a.id, 'b', "a should have b's id after reconcile")
    assert.equal(b.id, 'a', "b should have a's original id after reconcile")
    assert.deepEqual(
      [...result].map((x) => x.id),
      ['b', 'a'],
    )
  })
})
