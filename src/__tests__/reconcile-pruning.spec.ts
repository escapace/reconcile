import { assert, describe, it } from 'vitest'
import { isReconcileError, reconcile, ReconcileError } from '../index'
import { thrown } from './fixtures/thrown'

describe('identical-occupant pruning', () => {
  it('reads a pinned subtree once and never writes into it or verifies it', () => {
    let reads = 0
    const child = {
      nested: { deep: [1, 2, 3] },
      get value(): number {
        reads += 1
        return 1
      },
    }
    const nested = child.nested
    const current = { child, counter: 0 }
    const result = reconcile(current, { ...current, counter: 1 })
    assert.equal(result, current)
    assert.equal(current.counter, 1)
    assert.equal(current.child, child)
    assert.equal(child.nested, nested)
    assert.equal(reads, 1)
  })

  it('runs a getter again when next reaches it through an object that refers to current', () => {
    let reads = 0
    const placed = {
      get value(): number {
        reads += 1
        return 1
      },
    }
    const current: Record<string, unknown> = { b: placed }
    // eslint-disable-next-line perfectionist/sort-objects -- The reference to current is read first.
    const link = { up: current, p: placed }
    current.a = link
    const result = reconcile(current, { a: link, b: placed, n: 1 })
    assert.equal(result, current)
    assert.equal(current.a, link)
    assert.equal(current.b, placed)
    assert.equal(link.p, placed)
    assert.equal(current.n, 1)
    assert.equal(reads, 2)
  })

  it('captures a shared subtree that points at the next root so it reaches the live root', () => {
    const child: { n: number; up?: object } = { n: 0 }
    const current = { child, counter: 0 }
    const next = { child, counter: 1 }
    child.up = next
    const result = reconcile(current, next)
    assert.equal(result, current)
    assert.equal(current.child, child)
    assert.equal(child.up, current)
    assert.equal(current.counter, 1)
  })

  it('captures a subtree whose back reference reaches the current root, as before', () => {
    const current: { child: { n: number; parent?: object }; counter: number } = {
      child: { n: 0 },
      counter: 0,
    }
    current.child.parent = current
    const child = current.child
    const result = reconcile(current, { ...current, counter: 7 })
    assert.equal(result, current)
    assert.equal(current.child, child)
    assert.notEqual(child.parent, current)
    assert.equal((child.parent as { counter: number }).counter, 0)
    assert.equal(current.counter, 7)
  })

  it('never reuses an object inside a pinned subtree for another position', () => {
    const p = { x: 1 }
    const o = { ref: p }
    const current = { a: o, b: p }
    const result = reconcile(current, { a: o, b: { x: 2 } })
    assert.equal(result, current)
    assert.equal(current.a, o)
    assert.equal(o.ref, p)
    assert.equal(p.x, 1)
    assert.notEqual(current.b, p)
    assert.deepEqual(current.b, { x: 2 })
  })

  it('keeps sharing between a pinned subtree and other positions by identity', () => {
    const nodes = [{ n: 0 }, { n: 1 }, { n: 2 }]
    const current = { list: [nodes[0], undefined, nodes[1], nodes[0]], nodes }
    const result = reconcile(current, {
      list: [nodes[0], nodes[2], nodes[0], nodes[2]],
      nodes,
    })
    assert.equal(result, current)
    assert.equal(current.nodes, nodes)
    assert.deepEqual(
      nodes.map((node) => node.n),
      [0, 1, 2],
    )
    assert.deepEqual(current.list, [nodes[0], nodes[2], nodes[0], nodes[2]])
  })

  it('forces the pinned identity at every other position of the same object', () => {
    const left = { n: 1 }
    const right = { n: 2 }
    const current = { left, right }
    const result = reconcile(current, { left, right: left })
    assert.equal(result, current)
    assert.equal(current.left, left)
    assert.equal(current.right, left)
    assert.equal(left.n, 1)
    assert.equal(right.n, 2)
  })

  it('publishes a competing next object fresh when its occupant is pinned elsewhere', () => {
    const shared = { n: 0 }
    const current = { a: shared, b: shared }
    const result = reconcile(current, { a: { n: 5 }, b: shared })
    assert.equal(result, current)
    assert.equal(current.b, shared)
    assert.equal(shared.n, 0)
    assert.notEqual(current.a, shared)
    assert.equal(current.a.n, 5)
  })

  it('does not keep an object in place that next holds first at another position', () => {
    const placed = { n: 1 }
    const occupant = { n: 0 }
    const current = { a: occupant, b: placed }
    const result = reconcile(current, { a: placed, b: placed })
    assert.equal(result, current)
    // placed is matched at a, where current holds occupant, so occupant takes its contents at both
    // positions and current drops placed.
    assert.equal(current.a, occupant)
    assert.equal(current.b, occupant)
    assert.equal(occupant.n, 1)
    assert.equal(placed.n, 1)
  })

  it('keeps an object that next holds first elsewhere when it is inside an object that stays', () => {
    const placed = { n: 1 }
    const occupant = { n: 0 }
    const box = { placed }
    const current = { a: occupant, b: box }
    const result = reconcile(current, { a: placed, b: box })
    assert.equal(result, current)
    assert.equal(current.a, placed)
    assert.equal(current.b, box)
    assert.equal(box.placed, placed)
    assert.equal(placed.n, 1)
    assert.equal(occupant.n, 0)
  })

  it('never writes into a frozen pinned subtree', () => {
    const frozen = Object.freeze({ list: Object.freeze([1]), n: 0 })
    const current = { counter: 0, frozen }
    const result = reconcile(current, { ...current, counter: 1 })
    assert.equal(result, current)
    assert.equal(current.frozen, frozen)
    assert.equal(current.counter, 1)
  })

  it('throws without writing when the current root cannot hold an object that stays', () => {
    // The root is frozen, or a is read-only and not configurable, or a getter without a setter.
    const blocks: Array<(root: object, other: object) => unknown> = [
      (root) => Object.freeze(root),
      (root) => Object.defineProperty(root, 'a', { configurable: false, writable: false }),
      (root, other) => Object.defineProperty(root, 'a', { get: () => other }),
    ]
    for (const block of blocks) {
      const placed = { n: 1 }
      const other = { n: 0 }
      const box = { placed }
      const current = { a: other, b: box }
      block(current, other)
      const caught = thrown(() => reconcile(current, { a: placed, b: box }))
      assert.ok(isReconcileError(caught) && caught.cause.type === 'PublicationRejected')
      assert.deepEqual(Object.keys(current), ['a', 'b'])
      assert.equal(current.a, other)
      assert.equal(current.b, box)
      assert.equal(box.placed, placed)
      assert.equal(other.n, 0)
    }
  })

  it('replaces a frozen object inside current that cannot hold an object that stays', () => {
    const placed = { n: 1 }
    const other = { n: 0 }
    const holder = Object.freeze({ item: other })
    const box = { placed }
    const current = { a: holder, b: box }
    const result = reconcile(current, { a: { item: placed }, b: box })
    assert.equal(result, current)
    assert.notEqual(current.a, holder)
    assert.equal(current.a.item, placed)
    assert.equal(holder.item, other)
    assert.equal(other.n, 0)
    assert.equal(current.b, box)
    assert.equal(box.placed, placed)
  })

  it('publishes a reference to the current root as a copy of its old state, as before', () => {
    const current: { counter: number; self?: object } = { counter: 0 }
    current.self = current
    const result = reconcile(current, { counter: 1, self: current })
    assert.equal(result, current)
    assert.equal(current.counter, 1)
    assert.notEqual(current.self, current)
    assert.equal((current.self as { counter: number }).counter, 0)
  })

  it('pins collections and dates but not buffers or views', () => {
    const buffer = new ArrayBuffer(4)
    const view = new Uint8Array(buffer)
    const map = new Map([[1, { n: 1 }]])
    const set = new Set([{ n: 2 }])
    const date = new Date(5)
    const current = { buffer, counter: 0, date, map, set, view }
    const result = reconcile(current, { ...current, counter: 1 })
    assert.equal(result, current)
    assert.equal(current.map, map)
    assert.equal(current.set, set)
    assert.equal(current.date, date)
    assert.equal(current.buffer, buffer)
    assert.equal(current.view, view)
    assert.equal(current.counter, 1)
  })

  it('never treats an object inside a Map or Set entry as already in place', () => {
    for (const wrap of [
      (entry: object) => new Map([['key', entry]]),
      (entry: object) => new Map([[entry, 'value']]),
      (entry: object) => new Set([entry]),
    ]) {
      const placed = { v: 'x' }
      const entry = { placed }
      const collection = wrap(entry)
      const current = { a: placed, b: collection }
      const result = reconcile(current, { a: { v: 'n' }, b: wrap({ placed }) })
      assert.equal(result, current)
      // placed is at entry.placed on both sides but not in place there, so current keeps it at a,
      // the first position read, and the entry receives a new object.
      assert.equal(current.a, placed)
      assert.equal(placed.v, 'n')
      assert.equal(current.b, collection)
      assert.include([...collection].flat(), entry)
      assert.notEqual(entry.placed, placed)
      assert.deepEqual(entry.placed, { v: 'x' })
    }
  })

  it('keeps an object in place at a property that next reads before a Map holding it', () => {
    const placed = { v: 'x' }
    const map = new Map<number, object>()
    const current = { a: placed, b: placed, m: map }
    const result = reconcile(current, { a: { v: 'n' }, b: placed, m: new Map([[1, placed]]) })
    assert.equal(result, current)
    assert.equal(current.b, placed)
    assert.equal(current.m, map)
    assert.equal(map.get(1), placed)
    assert.notEqual(current.a, placed)
    assert.deepEqual(current.a, { v: 'n' })
    assert.equal(placed.v, 'x')
  })

  it('walks a subtree that stays in place without reading the values it would copy', () => {
    // A proxy of a Date has no time of its own, so reading it throws; staying in place, it is
    // not read.
    const date = new Proxy(new Date(5), {})
    const url = new URL('https://example.test/?q=1')
    const view = new Uint8Array([1, 2])
    const kept = { date, url, view }
    const current = { counter: 0, kept }
    assert.equal(reconcile(current, { ...current, counter: 1 }), current)
    assert.equal(current.kept, kept)
    assert.equal(kept.date, date)
    assert.equal(kept.url, url)
    assert.equal(kept.view, view)
    assert.equal(current.counter, 1)
  })

  it('pins array elements and object slots inside arrays', () => {
    const items = [{ id: 1 }, { id: 2 }, { id: 3 }]
    const [first, second, third] = items
    const current = { items }
    const result = reconcile(current, { items: [first, second, third, { id: 4 }] })
    assert.equal(result, current)
    assert.equal(current.items, items)
    assert.equal(items[0], first)
    assert.equal(items[1], second)
    assert.equal(items[2], third)
    assert.deepEqual(items[3], { id: 4 })
  })

  it('still rejects an incompatible root and leaves earlier writes in place', () => {
    const child = { n: 0 }
    const current = { child, counter: 0 }
    assert.throws(() => reconcile(current, [1]), ReconcileError)
    const frozen = Object.freeze({ child, counter: 0, kept: child })
    assert.throws(() => reconcile(frozen, { child, counter: 1, kept: { n: 9 } }), ReconcileError)
    assert.equal(frozen.child, child)
    assert.equal(child.n, 0)
  })
})
