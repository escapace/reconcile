import { assert, it } from 'vitest'

import { isReconcileError, produce, reconcile, ReconcileError } from '../index'
import { thrown } from './fixtures/thrown'

it('retains a child reached through repeated fixed references and a fixed root cycle', () => {
  const child = { n: 0 }
  const current = { left: child, right: child, self: {} }
  current.self = current
  Object.freeze(current)
  const wanted = { n: 2 }
  const next = { left: wanted, right: wanted, self: {} }
  next.self = next

  assert.equal(reconcile(current, next), current)
  assert.equal(current.left, child)
  assert.equal(current.right, child)
  assert.equal(current.self, current)
  assert.equal(child.n, 2)
  assert.equal(wanted.n, 2)
})

it('rejects merging distinct fixed references before publishing any child', () => {
  const current = Object.freeze({ left: { n: 0 }, right: { n: 0 } })
  const wanted = { n: 1 }
  assert.throws(() => reconcile(current, { left: wanted, right: wanted }), ReconcileError)
  assert.equal(current.left.n, 0)
  assert.equal(current.right.n, 0)
  assert.notEqual(current.left, current.right)
})

it('rejects splitting one fixed identity into distinct requested nodes', () => {
  const child = { n: 0 }
  const current = Object.freeze({ left: child, right: child })
  assert.throws(() => reconcile(current, { left: { n: 1 }, right: { n: 2 } }), ReconcileError)
  assert.equal(child.n, 0)
  assert.equal(current.left, current.right)
})

it('rejects removing or changing a fixed scalar while accepting SameValue', () => {
  const current = Object.freeze({ n: Number.NaN })
  assert.equal(reconcile(current, { n: Number.NaN }), current)
  assert.throws(() => reconcile(current, {}), ReconcileError)
  assert.throws(() => reconcile(current, { n: 1 }), ReconcileError)
  assert.isNaN(current.n)
})

it('rejects a changed accessor whose setter does not store the value', () => {
  let writes = 0
  const current = {}
  Object.defineProperty(current, 'n', {
    configurable: true,
    enumerable: false,
    get: () => 0,
    set: () => {
      writes += 1
    },
  })
  assert.throws(() => reconcile(current, { n: 2 }), ReconcileError)
  assert.equal(writes, 1)
  assert.equal(typeof Object.getOwnPropertyDescriptor(current, 'n')?.get, 'function')
})

it('uses a fixed accessor setter when the requested value changes', () => {
  let stored = 0
  const current = {}
  const setter = (value: number) => {
    stored = value
  }
  Object.defineProperty(current, 'n', {
    configurable: false,
    enumerable: true,
    set: setter,
    get: () => stored,
  })
  assert.equal(reconcile(current, { n: 2 }), current)
  assert.equal(stored, 2)
  assert.include(Object.getOwnPropertyDescriptor(current, 'n'), { set: setter })
})

it('retries another aligned candidate after both assignment and definition fail', () => {
  const blocked = new Proxy({ n: 0 }, { defineProperty: () => false, set: () => false })
  const usable = { n: 0 }
  const current = { left: blocked, right: usable }
  const shared = { n: 4 }
  assert.equal(reconcile(current, { left: shared, right: shared }), current)
  assert.equal(current.left, usable)
  assert.equal(current.right, usable)
  assert.equal(usable.n, 4)
  assert.equal(blocked.n, 0)
  assert.equal(shared.n, 4)
})

it('propagates a root publication exception without rolling back earlier writes', () => {
  const failure = new Error('setter refused publication')
  const target = { first: 0, second: 0 }
  const current = new Proxy(target, {
    set(object, key, value, receiver) {
      if (key === 'second') throw failure
      return Reflect.set(object, key, value, receiver)
    },
  })
  const next = { first: 1, second: 2 }
  assert.throws(() => reconcile(current, next), failure)
  assert.deepEqual(target, { first: 1, second: 0 })
  assert.deepEqual(next, { first: 1, second: 2 })
})

it('propagates a nested setter, trap or method exception unchanged instead of replacing', () => {
  const failure = new Error('refused')
  const cases: Array<[object, object]> = [
    [
      {
        get s() {
          return 0
        },
        set s(_value: number) {
          throw failure
        },
      },
      { s: 1 },
    ],
    [
      new Proxy(
        { s: 0 },
        {
          set() {
            throw failure
          },
        },
      ),
      { s: 1 },
    ],
  ]
  for (const [inner, desired] of cases) {
    const current = { inner }
    assert.throws(() => reconcile(current, { inner: desired }), failure)
    assert.strictEqual(current.inner, inner)
  }
})

it.each(['object', 'array'] as const)('replaces a nested %s that refuses deletion', (kind) => {
  const target = kind === 'array' ? [1] : { obsolete: 1 }
  const blocked = new Proxy(target, { deleteProperty: () => false })
  const desired = kind === 'array' ? new Array<number>(1) : {}
  const current = { child: blocked }
  assert.equal(reconcile(current, { child: desired }), current)
  assert.notEqual(current.child, blocked)
  assert.deepEqual(Reflect.ownKeys(current.child), Reflect.ownKeys(desired))
  assert.deepEqual(Reflect.ownKeys(target), kind === 'array' ? ['0', 'length'] : ['obsolete'])
})

it('rejects adding a property to a non-extensible root before updating existing values', () => {
  const current = Object.preventExtensions({ n: 0 })
  const next = Object.fromEntries([
    ['n', 1],
    ['added', 2],
  ])
  assert.throws(() => reconcile(current, next), ReconcileError)
  assert.deepEqual(current, { n: 0 })
})

it('removes obsolete numeric keys while relocating names independently', () => {
  const current = { 0: 0, a: 0, b: 0 }
  const next = Object.fromEntries([
    ['b', 2],
    ['a', 1],
  ])
  assert.equal(reconcile(current, next), current)
  assert.deepEqual(Reflect.ownKeys(current), ['b', 'a'])
  assert.deepEqual(current, next)
})

it('counts distinct views of one buffer without losing the shared requested view', () => {
  const buffer = new ArrayBuffer(4)
  const first = new Uint8Array(buffer)
  const second = new Uint8Array(buffer)
  const current = { first, second }
  const wanted = new Uint8Array([1, 2, 3, 4])
  assert.equal(reconcile(current, { first: wanted, second: wanted }), current)
  assert.equal(current.first, first)
  assert.equal(current.second, first)
  assert.equal(current.first.buffer, buffer)
  assert.deepEqual([...first], [1, 2, 3, 4])
  assert.deepEqual([...wanted], [1, 2, 3, 4])
})

it('caller publication propagates publication failure without exposing isolated recipe writes on current', () => {
  const current = Object.preventExtensions({ n: 0 })
  assert.throws(
    () =>
      reconcile(
        current,
        produce(current, (draft) => {
          draft.n = 1
          return { added: 2, n: draft.n }
        }),
      ),
    ReconcileError,
  )
  assert.deepEqual(current, { n: 0 })
})

// A proxy that refuses to store a value above 10.
const guarded = () =>
  new Proxy<{ a: number }>(
    { a: 1 },
    {
      set: (target, key, value: number) => value <= 10 && Reflect.set(target, key, value),
    },
  )

it("respects a proxy's refused assignment instead of defining the value past it", () => {
  const nested = guarded()
  const current = { nested }
  reconcile(current, { nested: { a: 20 } })
  // The proxy blocks the change, so it is replaced, as an object with a setter that does not
  // store its value is.
  assert.notEqual(current.nested, nested)
  assert.equal(nested.a, 1)
  assert.equal(current.nested.a, 20)
  const root = guarded()
  assert.throws(() => reconcile(root, { a: 20 }), ReconcileError)
  assert.equal(root.a, 1)
})

it('redefines a read-only configurable property, keeping its attributes', () => {
  const current = {}
  Object.defineProperty(current, 'a', { configurable: true, enumerable: true, value: 1 })
  reconcile(current, { a: 2 })
  assert.deepEqual(Object.getOwnPropertyDescriptor(current, 'a'), {
    configurable: true,
    enumerable: true,
    value: 2,
    writable: false,
  })
})

/** A proxy over an extensible target may list a key it reports no descriptor for. */
const ghost = (): Record<string, unknown> =>
  new Proxy({}, { getOwnPropertyDescriptor: () => undefined, ownKeys: () => ['ghost'] })

it('treats a key a proxy lists without a descriptor as absent', () => {
  const caught = thrown(() => reconcile(ghost(), { a: 1 }))
  assert.ok(isReconcileError(caught) && caught.cause.type === 'PublicationRejected')
  // Inside current, the proxy is replaced by a new object, as any object that cannot hold next is.
  const current = { x: ghost() }
  const held = current.x
  const result = reconcile(current, { x: { a: 1 } })
  assert.equal(result, current)
  assert.notEqual(result.x, held)
  assert.deepEqual(result.x, { a: 1 })
})
