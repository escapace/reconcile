import { assert, it } from 'vitest'

import { produce, reconcile, ReconcileError } from '../index'

it('captures array growth caused by a requested indexed getter', () => {
  const current: number[] = []
  const next = [0]
  let reads = 0
  Object.defineProperty(next, '0', {
    configurable: true,
    enumerable: true,
    get() {
      reads += 1
      next[2] = 3
      return 1
    },
  })
  assert.equal(reconcile(current, next), current)
  assert.equal(reads, 1)
  assert.equal(current.length, 3)
  assert.equal(current[0], 1)
  assert.isFalse(1 in current)
  assert.equal(current[2], 3)
})

it('publishes root cycles through objects, Map keys, Map values, and Sets', () => {
  const current = { map: new Map<object, object>(), self: {}, set: new Set<object>() }
  const next = { map: new Map<object, object>(), self: {}, set: new Set<object>() }
  next.self = next
  next.map.set(next, next)
  next.set.add(next)
  const map = current.map
  const set = current.set
  assert.equal(reconcile(current, next), current)
  assert.equal(current.self, current)
  assert.equal(current.map, map)
  assert.equal(current.map.get(current), current)
  assert.equal(current.set, set)
  assert.isTrue(current.set.has(current))
})

it('retains a mutable child behind a read-only root reference', () => {
  const child = { n: 0 }
  const current = Object.freeze({ child })
  assert.equal(reconcile(current, { child: { n: 1 } }), current)
  assert.equal(current.child, child)
  assert.equal(child.n, 1)
})

it('replaces an incompatible nested array while preserving the root and sibling', () => {
  const prototype = Object.create(Array.prototype) as number[]
  prototype[0] = 7
  const array = new Array<number>(1)
  Object.setPrototypeOf(array, prototype)
  const sibling = { n: 0 }
  const current = { array, sibling }
  assert.equal(reconcile(current, { array: new Array<number>(1), sibling: { n: 2 } }), current)
  assert.notEqual(current.array, array)
  assert.isFalse(0 in current.array)
  assert.equal(current.sibling, sibling)
  assert.equal(sibling.n, 2)
})

it('repairs a nested setter that reports success without publishing', () => {
  const child = new Proxy({ n: 0 }, { set: () => true })
  const sibling = { n: 0 }
  const current = { child, sibling }
  assert.equal(reconcile(current, { child: { n: 1 }, sibling: { n: 2 } }), current)
  assert.notEqual(current.child, child)
  assert.equal(current.child.n, 1)
  assert.equal(current.sibling, sibling)
  assert.equal(sibling.n, 2)
})

it('throws if the root setter reports success without publishing', () => {
  const current = new Proxy({ n: 0 }, { set: () => true })
  assert.throws(() => reconcile(current, { n: 1 }), ReconcileError)
})

it('tries another aligned identity after a descriptor conflict', () => {
  const first = Object.freeze({ n: 0 })
  const second = { n: 0 }
  const current = { first, second }
  const shared = { n: 1 }
  assert.equal(reconcile(current, { first: shared, second: shared }), current)
  assert.equal(current.first, second)
  assert.equal(current.second, second)
  assert.equal(second.n, 1)
})

it('restores a cycle as a group and keeps an actual edit isolated', () => {
  const current = { child: { n: 0, parent: {} }, self: {} }
  current.self = current
  current.child.parent = current
  const result = produce(current, (draft) => {
    draft.child.n = 1
    draft.child.n = 0
    return draft
  })
  assert.equal(result, current)
  const changed = produce(current, (draft) => {
    draft.child.n = 2
    return draft
  })
  assert.notEqual(changed, current)
  assert.equal(changed.self, changed)
  assert.equal(changed.child.parent, changed)
  assert.equal(changed.child.n, 2)
  assert.equal(current.child.n, 0)
})

it('retains explicit equal-but-distinct recipe replacements', () => {
  const current = { child: { n: 0 } }
  const authored = { n: 0 }
  const result = produce(current, (draft) => {
    draft.child = authored
    return draft
  })
  assert.notEqual(result, current)
  assert.equal(result.child, authored)
})

it('captures finalization getters once and incorporates their writes before publication', () => {
  let observations = 0
  const current = {
    n: 0,
    get computed() {
      observations += 1
      return ++this.n
    },
  }
  const next = produce(current, (draft) => draft)
  assert.equal(observations, 1)
  assert.equal(current.n, 0)
  assert.equal(next.n, 1)
  assert.equal(next.computed, 1)
  assert.isTrue('value' in Object.getOwnPropertyDescriptor(next, 'computed')!)
})

it('includes later getter writes to an earlier sibling without observing getters again', () => {
  let observations = 0
  const current = {
    left: { n: 0 },
    get computed() {
      observations += 1
      return ++this.left.n
    },
  }
  const next = produce(current, (draft) => draft)
  assert.equal(observations, 1)
  assert.equal(current.left.n, 0)
  assert.equal(next.left.n, 1)
  assert.equal(next.computed, 1)
})

it('caller publication composes finalization and publication onto the same root', () => {
  const current = { child: { n: 0 } }
  const child = current.child
  assert.equal(
    reconcile(
      current,
      produce(current, (draft) => {
        draft.child.n = 3
        return draft
      }),
    ),
    current,
  )
  assert.equal(current.child, child)
  assert.equal(current.child.n, 3)
})

it('ignores non-index array metadata when publishing the indexed payload', () => {
  const current = [0]
  const metadata = { n: 7 }
  Object.defineProperty(current, 'metadata', { value: metadata })
  assert.equal(reconcile(current, [1]), current)
  assert.equal(current[0], 1)
  assert.equal(Reflect.get(current, 'metadata'), metadata)
})

it('rejects impossible key order on a non-extensible root before deleting keys', () => {
  const current = Object.preventExtensions(
    Object.fromEntries([
      ['a', 0],
      ['b', 0],
    ]),
  )
  const next = Object.fromEntries([
    ['b', 1],
    ['a', 2],
  ])
  assert.throws(() => reconcile(current, next), ReconcileError)
  assert.deepEqual(Reflect.ownKeys(current), ['a', 'b'])
  assert.equal(current.a, 0)
})

it('selects the aligned buffer that also retains compatible dependent views', () => {
  const first = new ArrayBuffer(8)
  const second = new ArrayBuffer(8)
  const retained = new Uint16Array(second)
  const current = { first: new Uint8Array(first), second: retained }
  const buffer = new ArrayBuffer(8)
  new Uint8Array(buffer)[0] = 3
  const next = { first: new Uint16Array(buffer), second: new Uint16Array(buffer) }
  const result: unknown = reconcile(current, next)
  assert.equal(result, current)
  assert.equal(current.second, retained)
  assert.equal(current.first.buffer, second)
  assert.equal(current.second.buffer, second)
  assert.equal(new Uint8Array(second)[0], 3)
})
