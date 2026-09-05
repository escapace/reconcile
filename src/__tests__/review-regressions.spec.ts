import { assert, describe, it } from 'vitest'
import { createPatch, reconcile, snapshot } from '../index'

describe('review regressions', () => {
  for (const parentFirst of [true, false]) {
    it(`preserves distinct descendants of shared subtrees (parent first: ${parentFirst})`, () => {
      const child = { n: 1 }
      const parent = { child }
      const current = { a: parent, b: child }
      const next = { a: parent, b: { n: 2 } }
      if (!parentFirst) {
        Reflect.deleteProperty(current, 'a')
        current.a = parent
        Reflect.deleteProperty(next, 'a')
        next.a = parent
      }
      const result = reconcile(current, next)
      assert.equal(result, current)
      assert.equal(result.a.child.n, 1)
      assert.equal(result.b.n, 2)
      assert.notEqual(result.a.child, result.b)
    })
  }

  it('preserves original next edges after an earlier branch replaces a shared child', () => {
    const child = { n: 1 }
    const shared = { child }
    const current = { a: shared, b: shared, c: child }
    const result = reconcile(current, { a: { child: 7 }, b: shared, c: child })
    assert.equal(result.a.child, 7)
    assert.equal(result.b.child, result.c)
    assert.equal(result.c.n, 1)
  })

  it('preserves sharing through maps and sets inside an unchanged parent', () => {
    const child = { n: 1 }
    const parent = { map: new Map([[child, child]]), set: new Set([child]) }
    const current = { a: parent, b: child }
    const result = reconcile(current, { a: parent, b: { n: 2 } })
    const [[key, value]] = result.a.map
    assert.equal(key, value)
    assert.equal(result.a.set.has(value), true)
    assert.notEqual(value, result.b)
    assert.equal(value.n, 1)
    assert.equal(result.b.n, 2)
  })

  it('preserves an unchanged view while splitting its separately updated buffer', () => {
    const view = new Uint8Array([1, 2])
    const current = { a: { view }, b: view.buffer }
    const result = reconcile(current, {
      a: current.a,
      b: new Uint8Array([3, 4]).buffer,
    })
    assert.deepEqual(Array.from(result.a.view), [1, 2])
    assert.deepEqual(Array.from(new Uint8Array(result.b)), [3, 4])
    assert.notEqual(result.a.view.buffer, result.b)
  })

  it('redirects a mutual cycle through an unchanged ancestor to the finalized root', () => {
    interface Root {
      c: { n: number }
      b?: { a: Root }
    }
    // Visit the back-reference before the changed descendant.
    const root: Root = { b: undefined, c: { n: 1 } }
    root.b = { a: root }
    const result = createPatch(root, (draft) => {
      draft.c.n = 2
      return draft
    })
    assert.equal(result.b!.a, result)
    assert.equal(result.b!.a.c.n, 2)
    assert.equal(root.b.a, root)
    assert.equal(root.c.n, 1)
  })

  it('retains unchanged mutual cycles by identity', () => {
    const root: { self?: { root: unknown } } = {}
    root.self = { root }
    assert.equal(
      createPatch(root, (draft) => draft),
      root,
    )
  })

  it('snapshots an own __proto__ data property without changing the prototype', () => {
    const source = { ['__proto__']: { n: 1 } }
    const result = snapshot(source) as typeof source
    assert.deepEqual(Reflect.ownKeys(result), ['__proto__'])
    assert.equal(Object.getPrototypeOf(result), Object.prototype)
    assert.deepEqual(Object.getOwnPropertyDescriptor(result, '__proto__')?.value as unknown, {
      n: 1,
    })
    assert.notEqual(
      Object.getOwnPropertyDescriptor(result, '__proto__')?.value as unknown,
      Object.getOwnPropertyDescriptor(source, '__proto__')?.value as unknown,
    )
  })

  for (const current of [{}, { before: 1 }]) {
    it(`reconciles an own __proto__ property with ${Reflect.ownKeys(current).length} existing keys`, () => {
      const source = { ['__proto__']: { n: 1 } }
      const result = reconcile(current, source)
      assert.deepEqual(Reflect.ownKeys(result), ['__proto__'])
      assert.equal(Object.getPrototypeOf(result), Object.prototype)
      assert.deepEqual(Object.getOwnPropertyDescriptor(result, '__proto__')?.value as unknown, {
        n: 1,
      })
      assert.equal(Object.hasOwn(Object.prototype, 'n'), false)
    })
  }

  it('materializes an own undefined __proto__ value', () => {
    const result = reconcile({}, { ['__proto__']: undefined })
    assert.equal(Object.hasOwn(result, '__proto__'), true)
    assert.equal(Object.getOwnPropertyDescriptor(result, '__proto__')?.value as unknown, undefined)
    assert.equal(Object.getPrototypeOf(result), Object.prototype)
  })

  it('retains an existing own __proto__ value by identity', () => {
    const value = { n: 1 }
    const current = { ['__proto__']: value }
    const result = reconcile(current, { ['__proto__']: { n: 2 } })
    assert.equal(Object.getOwnPropertyDescriptor(result, '__proto__')?.value as unknown, value)
    assert.equal(value.n, 2)
    assert.equal(Object.getPrototypeOf(result), Object.prototype)
  })

  it('preserves __proto__ in a nested replacement snapshot', () => {
    const source = { ['__proto__']: { n: 1 } }
    const result = reconcile({ child: null }, { child: source })
    assert.deepEqual(Reflect.ownKeys(result.child), ['__proto__'])
    assert.equal(Object.getPrototypeOf(result.child), Object.prototype)
  })

  it('invalidates cached array children when length shrinks and grows again', () => {
    const current = [{ n: 1 }, { n: 2 }]
    const result = createPatch(current, (draft) => {
      const retained = draft[0]
      const removed = draft[1]
      draft.length = 1
      assert.equal(draft[0], retained)
      assert.equal(draft[1], undefined)
      assert.equal(1 in draft, false)
      draft.length = 2
      assert.equal(draft[1], undefined)
      assert.equal(1 in draft, false)
      removed.n = 3
      return draft
    })
    assert.equal(result.length, 2)
    assert.equal(1 in result, false)
    assert.equal(current[1].n, 2)
  })
})
