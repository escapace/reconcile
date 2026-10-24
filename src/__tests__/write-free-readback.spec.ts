import { assert, describe, it } from 'vitest'
import { isReconcileError, reconcile } from '../index'

/** A proxy over `target` that records `ownKeys` and write traps. */
function counted(target: object, log: string[]): object {
  return new Proxy(target, {
    defineProperty(object, key, descriptor) {
      log.push(`define ${String(key)}`)
      return Reflect.defineProperty(object, key, descriptor)
    },
    ownKeys(object) {
      log.push('keys')
      return Reflect.ownKeys(object)
    },
    set(object, key, value, receiver) {
      log.push(`set ${String(key)}`)
      return Reflect.set(object, key, value, receiver)
    },
  })
}

it('answers the readback of a publication that wrote nothing without reading again', () => {
  const log: string[] = []
  const current = { a: 1, b: [2, 3] }
  const proxy = counted(current, log)
  assert.strictEqual(reconcile(proxy, { a: 1, b: [2, 3] }), proxy)
  // The preflight lists the keys once (names, then symbols); no write and no readback follow.
  assert.deepEqual(log, ['keys', 'keys'])
})

it('reads back a publication that wrote', () => {
  const log: string[] = []
  const proxy = counted({ a: 1, b: 2 }, log)
  reconcile(proxy, { a: 1, b: 3 })
  assert.deepEqual(log.slice(-2), ['keys', 'keys'], 'the readback lists the keys again')
  assert.ok(log.some((entry) => entry.startsWith('set')))
})

it('reads back after a setter changes a key that publication already compared', () => {
  let stored = 1
  const current = {
    b: 1,
    get a(): number {
      return stored
    },
    set a(value: number) {
      // A setter is application code; it may change other state, which readback must see.
      stored = value
      this.b = 99
    },
  }
  let failure: unknown
  try {
    // `b` comes first, as in `current`, so `a`'s setter runs after `b` was compared.
    reconcile(
      current,
      Object.fromEntries([
        ['b', 1],
        ['a', 2],
      ]),
    )
  } catch (error) {
    failure = error
  }
  assert.ok(isReconcileError(failure) && failure.cause.type === 'PublicationRejected')
  assert.strictEqual(current.b, 99)
})

it('decides a later object key from its read before the first write, so a setter that changes it blocks the change', () => {
  const child = { n: 1 }
  const other = { n: 2 }
  const make = () => {
    let stored = 1
    return {
      get a(): number {
        return stored
      },
      set a(value: number) {
        stored = value
        this.b = other
      },
      // eslint-disable-next-line perfectionist/sort-objects -- `a` publishes before `b`
      b: child,
    }
  }
  const current = make()
  let failure: unknown
  try {
    // Capture read `b` as `child`, which `next` keeps there, so it is not written after `a`'s
    // setter changes it; the readback rejects the result (WriteFreeReadback.publishPre).
    reconcile(current, { a: 2, b: child })
  } catch (error) {
    failure = error
  }
  assert.ok(isReconcileError(failure) && failure.cause.type === 'PublicationRejected')
  assert.strictEqual(current.b, other)
  // Inside `current`, the object that blocks the change is replaced instead.
  const inner = make()
  const nested = { inner }
  reconcile(nested, { inner: { a: 2, b: child } })
  assert.notStrictEqual(nested.inner, inner)
  assert.deepEqual(nested.inner, { a: 2, b: child })
  assert.strictEqual(nested.inner.b, child)
})

/** An object holding an own getter and setter `g`, which count their calls, then `other`. Each
 * `next` lists keys in this order: reordering them is a write. */
function counting(value: unknown): { calls: { reads: number; writes: number }; root: object } {
  const calls = { reads: 0, writes: 0 }
  const root: Record<string, unknown> = {}
  Object.defineProperty(root, 'g', {
    configurable: true,
    enumerable: true,
    get: () => {
      calls.reads += 1
      return value
    },
    set: (written: unknown) => {
      calls.writes += 1
      value = written
    },
  })
  root.other = 1
  return { calls, root }
}

describe('a getter of current runs once without writes and twice with them', () => {
  const child = { c: 1 }
  it.each([
    ['a primitive, nothing written', 1, 1, 1, 1, 0],
    ['a primitive, another key written', 1, 1, 2, 2, 0],
    ['a primitive, written through its setter', 1, 2, 1, 2, 1],
    ['a kept object, nothing written', child, child, 1, 1, 0],
    ['a kept object, another key written', child, child, 2, 2, 0],
    ['an object, written through its setter', null, { c: 2 }, 1, 2, 1],
  ])('%s', (_label, held, wanted, other, reads, writes) => {
    const { calls, root } = counting(held)
    reconcile({ root }, { root: { g: wanted, other } })
    assert.deepEqual(calls, { reads, writes })
  })

  it('runs a getter without a setter, which must already hold its value, as often', () => {
    for (const [other, reads] of [
      [1, 1],
      [2, 2],
    ]) {
      let calls = 0
      const root: Record<string, unknown> = {}
      Object.defineProperty(root, 'g', {
        configurable: true,
        enumerable: true,
        get: () => {
          calls += 1
          return 5
        },
      })
      root.other = 1
      reconcile({ root }, { root: { g: 5, other } })
      assert.equal(calls, reads)
    }
  })

  it('runs it once more for each retried plan', () => {
    // A setter that does not store its value makes the readback reject the plan that keeps its
    // object, and the retry replaces that object.
    const stubborn: Record<string, unknown> = {}
    Object.defineProperty(stubborn, 'g', {
      configurable: true,
      enumerable: true,
      get: () => 1,
      set: () => undefined,
    })
    stubborn.other = 1
    const { calls, root } = counting(1)
    const current = { root, stubborn }
    reconcile(current, { root: { g: 1, other: 1 }, stubborn: { g: 2, other: 1 } })
    assert.notStrictEqual(current.stubborn, stubborn)
    assert.deepEqual(calls, { reads: 3, writes: 0 })
  })

  it('reads a getter of another object aligned with one node once before the first write', () => {
    const log: string[] = []
    const getterOnly = (name: string): object => {
      const object = { k: 1 }
      const value = { z: 1 }
      Object.defineProperty(object, 'g', {
        configurable: true,
        enumerable: true,
        get: () => {
          log.push(`${name}.g`)
          return value
        },
      })
      return object
    }
    const current = counted({ a: getterOnly('X'), b: getterOnly('Y') }, log)
    const shared = { g: { z: 1 }, k: 1 }
    reconcile(current, { a: shared, b: shared })
    const first = log.findIndex((entry) => entry.startsWith('set') || entry.startsWith('define'))
    assert.deepEqual(
      log.slice(0, first).filter((entry) => entry.endsWith('.g')),
      ['X.g', 'Y.g'],
    )
  })

  it('counts a proxy get trap as a getter call', () => {
    for (const [other, gets] of [
      [1, 1],
      [2, 2],
    ]) {
      let count = 0
      const root = new Proxy(
        { o: child, other: 1 },
        {
          get(target, key, receiver) {
            if (key === 'o') count += 1
            return Reflect.get(target, key, receiver) as unknown
          },
        },
      )
      reconcile({ root }, { root: { o: child, other } })
      assert.equal(count, gets)
    }
  })

  it.each([
    ['Date', () => new Date(1)],
    ['Map', () => new Map([[1, 2]])],
    ['Set', () => new Set([1])],
    ['URL', () => new URL('https://example.test/?a=1')],
    ['URLSearchParams', () => new URLSearchParams('a=1')],
    ['ArrayBuffer', () => new Uint8Array([1, 2]).buffer],
    ['Uint8Array', () => new Uint8Array([1, 2])],
  ])('reads it once when a %s next to it compared equal', (_label, make) => {
    const { calls, root } = counting(1)
    reconcile({ native: make(), root }, { native: make(), root: { g: 1, other: 1 } })
    assert.deepEqual(calls, { reads: 1, writes: 0 })
  })
})

it("reads a mismatched occupant's prototype once", () => {
  let reads = 0
  const occupant = new Proxy(
    { x: 1 },
    {
      getPrototypeOf(target) {
        reads += 1
        return Reflect.getPrototypeOf(target)
      },
    },
  )
  reconcile({ a: occupant }, { a: [1] })
  assert.equal(reads, 1)
})
