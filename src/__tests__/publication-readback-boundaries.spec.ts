import { assert, it } from 'vitest'
import { reactive, readonly, toRaw } from 'vue'

import { reconcile, ReconcileError, snapshot } from '../index'

it.each([false, true])(
  'keeps fresh shells writable after readonly exposure (detached next: %s)',
  (detached) => {
    const oldSet = new Set<object>()
    const oldArray: object[] = []
    oldArray.push(readonly(oldArray))
    const oldMap = new Map<object, object>([
      [readonly(oldSet), oldArray],
      // eslint-disable-next-line perfectionist/sort-maps -- Entry order determines aligned candidates.
      [oldSet, oldSet],
    ])
    const current = { child: { set: oldSet }, map: readonly(oldMap) }
    const set = new Set<object>()
    const array = [readonly(set)]
    const object = { set: readonly(set) }
    const map = new Map<object, object>([
      [readonly(set), array],
      // eslint-disable-next-line perfectionist/sort-maps -- Match the current Map's candidate order.
      [object, array],
    ])
    set.add(array)
    set.add(map)
    const source = { child: object, map: readonly(map) }
    const expected = snapshot(source) as typeof source
    const next = detached ? (snapshot(source) as typeof source) : source

    const result = reconcile(current, next)
    assert.equal(result, current)
    assert.deepEqual(snapshot(result), expected)
    assert.deepEqual(snapshot(source), expected)
    const images = new Map<object, object>()
    const storage = new Set<object>()
    const edges = (value: object): unknown[] =>
      value instanceof Map
        ? [...value].flat()
        : value instanceof Set
          ? [...value]
          : Object.values(value)
    const check = (before: object, after: object): void => {
      if (images.has(before)) {
        assert.equal(after, images.get(before))
        return
      }
      assert.isFalse(storage.has(toRaw(after)))
      images.set(before, after)
      storage.add(toRaw(after))
      const children = edges(after)
      edges(before).forEach((child, index) => check(child as object, children[index] as object))
    }
    check(expected, result)
  },
)

it('republishes cyclic edges before checking nodes after a wrapper rebind', () => {
  const shared = reactive({})
  const left = { next: shared }
  const current = { left, right: shared }
  const a: { next?: object } = {}
  const b = { next: a }
  a.next = b
  const next = { left: { next: a }, right: { next: b } }

  const result = reconcile(current, next)
  assert.equal(result, current)
  assert.equal(result.left, left)
  assert.equal(result.left.next.next, result.right.next)
  assert.equal(result.right.next.next, result.left.next)
  const nodes = [result, result.left, result.right, result.left.next, result.right.next]
  assert.equal(new Set(nodes).size, nodes.length)
  assert.equal(new Set(nodes.map((node) => toRaw(node))).size, nodes.length)
  assert.equal(next.left.next, a)
  assert.equal(next.right.next, b)
  assert.equal(a.next, b)
  assert.equal(b.next, a)
})

// These fixtures deliberately provide unusable publication operations. A successful
// write result alone cannot certify publication; nested candidates can be replaced.
it.each(['length', 'value', 'own hole', 'inherited hole'] as const)(
  'repairs an array whose publication leaves an incorrect %s',
  (failure) => {
    const base = [0]
    const prototype = Object.create(Array.prototype) as number[]
    Object.setPrototypeOf(base, prototype)
    const blocked = new Proxy(base, {
      deleteProperty(target, key) {
        if (failure === 'own hole') return true
        const removed = Reflect.deleteProperty(target, key)
        if (failure === 'inherited hole') prototype[0] = 9
        return removed
      },
      set(target, key, value) {
        const written = Reflect.set(target, key, value)
        if (key === '0' && failure === 'length') target.length = 2
        if (key === '0' && failure === 'value') target[0] = 9
        return written
      },
    })
    const next = failure === 'length' || failure === 'value' ? [1] : new Array<number>(1)
    const current = { left: blocked, right: blocked }
    assert.equal(reconcile(current, { left: next, right: next }), current)
    assert.notEqual(current.left, blocked)
    assert.equal(current.left, current.right)
    assert.equal(current.left.length, 1)
    assert.equal(0 in current.left, 0 in next)
    assert.equal(current.left[0], next[0])
    assert.equal(Object.getPrototypeOf(current.left), Array.prototype)
    assert.equal(next.length, 1)
  },
)

it('repairs an object whose setter introduces an unwanted own property', () => {
  const blocked = new Proxy(
    { n: 0 },
    {
      set(target, key, value, receiver) {
        Reflect.set(target, 'extra', 9)
        return Reflect.set(target, key, value, receiver)
      },
    },
  )
  const current = { child: blocked }
  const next = { child: { n: 1 } }
  assert.equal(reconcile(current, next), current)
  assert.notEqual(current.child, blocked)
  assert.deepEqual(current.child, { n: 1 })
  assert.deepEqual(Reflect.ownKeys(current.child), ['n'])
  assert.deepEqual(next, { child: { n: 1 } })
})

it.each(['missing entry', 'wrong key', 'wrong value'] as const)(
  'repairs a Map whose set operation leaves a %s',
  (failure) => {
    const blocked = new Map([['old', 0]])
    Object.defineProperty(blocked, 'set', {
      value(key: string, value: number) {
        if (failure === 'missing entry') return blocked
        return Map.prototype.set.call(
          blocked,
          failure === 'wrong key' ? 'wrong' : key,
          failure === 'wrong value' ? 9 : value,
        )
      },
    })
    const current = { left: blocked, right: blocked }
    const next = new Map([['wanted', 1]])
    assert.equal(reconcile(current, { left: next, right: next }), current)
    assert.notEqual(current.left, blocked)
    assert.equal(current.left, current.right)
    assert.deepEqual([...current.left], [['wanted', 1]])
    assert.deepEqual([...next], [['wanted', 1]])
  },
)

it.each(['missing member', 'wrong member'] as const)(
  'repairs a Set whose add operation leaves a %s',
  (failure) => {
    const blocked = new Set([0])
    Object.defineProperty(blocked, 'add', {
      value() {
        return failure === 'missing member' ? blocked : Set.prototype.add.call(blocked, 9)
      },
    })
    const current = { left: blocked, right: blocked }
    const next = new Set([1])
    assert.equal(reconcile(current, { left: next, right: next }), current)
    assert.notEqual(current.left, blocked)
    assert.equal(current.left, current.right)
    assert.deepEqual([...current.left], [1])
    assert.deepEqual([...next], [1])
  },
)

// An object whose setter runs `effect` when publication writes its value: a write that changes
// bytes the engine already published, so readback rejects them and the plan is repaired.
function trigger(effect: () => void): { value: number; writes: () => number } {
  let stored = 0
  let writes = 0
  return {
    get value(): number {
      return stored
    },
    set value(next: number) {
      writes += 1
      effect()
      stored = next
    },
    writes: () => writes,
  }
}

it('repairs a buffer after a later publication changes its bytes', () => {
  const buffer = new ArrayBuffer(4)
  const hook = trigger(() => {
    new Uint8Array(buffer)[0] = 9
  })
  const current = { buffer, hook }
  const nextBuffer = new Uint8Array([1, 2, 3, 4]).buffer
  assert.equal(
    reconcile(current, { buffer: nextBuffer, hook: { value: 1, writes: hook.writes } }),
    current,
  )
  assert.notEqual(current.buffer, buffer)
  assert.equal(current.hook, hook)
  assert.equal(hook.value, 1)
  assert.equal(current.buffer.byteLength, 4)
  assert.deepEqual([...new Uint8Array(current.buffer)], [1, 2, 3, 4])
  assert.deepEqual([...new Uint8Array(nextBuffer)], [1, 2, 3, 4])
})

it('throws rather than reporting success when a root Map cannot publish its entries', () => {
  const current = new Map([['old', 0]])
  Object.defineProperty(current, 'set', { value: () => current })
  const next = new Map([['wanted', 1]])
  assert.throws(() => reconcile(current, next), ReconcileError)
  assert.equal(current.size, 0)
  assert.deepEqual([...next], [['wanted', 1]])
})

it.each([false, true])(
  'rebuilds fresh views when their buffer is repaired (views first: %s)',
  (viewsFirst) => {
    const buffer = new ArrayBuffer(4)
    const hook = trigger(() => {
      new Uint8Array(buffer)[0] = 9
    })
    const sibling = { stable: true }
    const current = { buffer, hook, sibling }
    const nextBuffer = new Uint8Array([1, 2, 3, 4]).buffer
    const view = new Uint8Array(nextBuffer, 1, 2)
    const dataView = new DataView(nextBuffer, 1, 2)
    const next = viewsFirst
      ? {
          buffer: nextBuffer,
          dataView,
          hook: { value: 1, writes: hook.writes },
          repeated: view,
          sibling: { stable: true },
          view,
        }
      : {
          buffer: nextBuffer,
          dataView,
          hook: { value: 1, writes: hook.writes },
          repeated: view,
          sibling: { stable: true },
          view,
        }
    const result = reconcile(current, next)
    assert.equal(result, current)
    assert.notEqual(result.buffer, buffer)
    assert.equal(result.view.buffer, result.buffer)
    assert.equal(result.dataView.buffer, result.buffer)
    assert.equal(result.view, result.repeated)
    assert.equal(result.view.byteOffset, 1)
    assert.equal(result.view.byteLength, 2)
    assert.equal(result.dataView.byteOffset, 1)
    assert.equal(result.dataView.byteLength, 2)
    assert.deepEqual([...new Uint8Array(result.buffer)], [1, 2, 3, 4])
    assert.deepEqual([...new Uint8Array(nextBuffer)], [1, 2, 3, 4])
    assert.equal(result.hook, hook)
    assert.equal(result.sibling, sibling)
    // The repaired plan finds the hook's value already written.
    assert.equal(hook.writes(), 1)
  },
)

it('retains an aligned view over the replacement buffer after repair', () => {
  const first = new ArrayBuffer(4)
  const second = new ArrayBuffer(4)
  const firstView = new Uint8Array(first)
  const secondView = new Uint8Array(second)
  const hook = trigger(() => {
    new Uint8Array(first)[0] = 9
  })
  const current = { first, left: firstView, right: secondView, second, trigger: hook }
  const buffer = new Uint8Array([1, 2, 3, 4]).buffer
  const view = new Uint8Array(buffer)
  const result = reconcile(current, {
    first: buffer,
    left: view,
    right: view,
    second: buffer,
    trigger: { value: 1, writes: hook.writes },
  })
  assert.equal(result, current)
  assert.equal(result.first, second)
  assert.equal(result.second, second)
  assert.equal(result.left, secondView)
  assert.equal(result.right, secondView)
  assert.equal(result.left.buffer, result.first)
  assert.deepEqual([...result.left], [1, 2, 3, 4])
  assert.equal(hook.writes(), 1)
})

it('repairs a view across multiple buffer rejections without extra repair attempts', () => {
  const first = new ArrayBuffer(4)
  const second = new ArrayBuffer(4)
  const hook = trigger(() => {
    new Uint8Array(first)[0] = 9
    new Uint8Array(second)[0] = 9
  })
  const current = { first, second, trigger: hook }
  const buffer = new Uint8Array([1, 2, 3, 4]).buffer
  const result = reconcile(current, {
    first: buffer,
    second: buffer,
    trigger: { value: 1, writes: hook.writes },
    view: new Uint8Array(buffer),
  })
  assert.equal(result, current)
  // The trigger corrupts both buffers once; the repaired plan keeps one of them for both keys.
  assert.ok(result.first === first || result.first === second)
  assert.equal(result.first, result.second)
  assert.equal(result.view.buffer, result.first)
  assert.deepEqual([...result.view], [1, 2, 3, 4])
  assert.equal(hook.writes(), 1)
})
