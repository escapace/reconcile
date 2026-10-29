import { assert, describe, it } from 'vitest'
import { produce, snapshot } from '../index'

// A draft admits exactly the writes the result can carry and refuses the others like a
// non-extensible object, so a write is never accepted and then dropped; an unchanged object keeps
// its own accessors. lean/Produce/DraftSurface.lean proves both rules and
// scripts/check/bridges/draft-surface.ts compares them natively.

describe('drafts of built-ins refuse properties the result cannot carry', () => {
  it('throws on a new property of an array draft instead of dropping it', () => {
    assert.throws(
      () =>
        produce({ list: [1] }, (draft) => {
          ;(draft.list as unknown as Record<string, unknown>).meta = 1
          return draft
        }),
      TypeError,
    )
  })

  it('throws on a new property of a Map or Set draft', () => {
    for (const value of [new Map([[1, 2]]), new Set([1])])
      assert.throws(
        () =>
          produce({ value }, (draft) => {
            ;(draft.value as unknown as Record<string, unknown>).meta = 1
            return draft
          }),
        TypeError,
      )
  })

  it('throws on a new property of a Date, buffer, view or URL copy', () => {
    for (const value of [
      new Date(0),
      new ArrayBuffer(2),
      new Uint8Array(2),
      new DataView(new ArrayBuffer(2)),
      new URL('https://example.test/'),
    ])
      assert.throws(
        () =>
          produce({ value }, (draft) => {
            ;(draft.value as unknown as Record<string, unknown>).meta = 1
            return draft
          }),
        TypeError,
      )
  })

  it('still accepts element and length writes', () => {
    const result = produce({ bytes: new Uint8Array(2), list: [1, 2, 3] }, (draft) => {
      draft.list[0] = 9
      draft.list.length = 2
      draft.bytes[1] = 7
      return draft
    })
    assert.deepEqual(result.list, [9, 2])
    assert.deepEqual([...result.bytes], [0, 7])
  })
})

function withGetter(get: () => unknown): Record<string, unknown> {
  const target: Record<string, unknown> = { a: 1 }
  Object.defineProperty(target, 'value', { configurable: true, enumerable: true, get })
  return target
}

describe('produce keeps own accessors of an unchanged object', () => {
  it('keeps an untouched object with an own getter, and the getter', () => {
    const target = withGetter(() => 1)
    const result = produce({ count: 0, target }, (draft) => {
      draft.count = 1
      return draft
    })
    assert.strictEqual(result.target, target)
    assert.equal(typeof Object.getOwnPropertyDescriptor(result.target, 'value')?.get, 'function')
  })

  it('keeps an Error-like object whose own accessor returns a primitive', () => {
    const error = new (class Failure {
      message = 'boom'
    })()
    Object.defineProperty(error, 'trace', { configurable: true, get: () => 'at line 1' })
    const result = produce({ error, ok: false }, (draft) => {
      draft.ok = true
      return draft
    })
    assert.strictEqual(result.error, error)
  })

  it('rebuilds the object with data when its getter returns a changed value', () => {
    const child = { n: 0 }
    const target = withGetter(() => child)
    const result = produce({ child, target }, (draft) => {
      draft.child.n = 1
      return draft
    })
    assert.notStrictEqual(result.target, target)
    assert.strictEqual(Object.getOwnPropertyDescriptor(result.target, 'value')?.value, result.child)
  })

  it('rebuilds the object when its own data changes', () => {
    const target = withGetter(() => 1)
    const result = produce({ target }, (draft) => {
      draft.target.a = 2
      return draft
    })
    assert.notStrictEqual(result.target, target)
    assert.equal(Object.getOwnPropertyDescriptor(result.target, 'value')?.value, 1)
  })

  it('never keeps a getter that returned a draft', () => {
    const child = { n: 0 }
    let draftChild: object | undefined
    const target = withGetter(() => draftChild)
    const result = produce({ child, target }, (draft) => {
      draftChild = draft.child
      return draft
    })
    assert.notStrictEqual(result.target, target)
    assert.strictEqual(Object.getOwnPropertyDescriptor(result.target, 'value')?.value, child)
  })

  it('keeps an array with an index getter by the same rule as an object', () => {
    let reads = 0
    const list: unknown[] = [1]
    Object.defineProperty(list, 1, {
      configurable: true,
      enumerable: true,
      get: () => (reads += 1),
    })
    const kept = produce({ count: 0, list }, (draft) => {
      draft.count = 1
      return draft
    })
    assert.strictEqual(kept.list, list)
    assert.equal(reads, 1)
    const rebuilt = produce({ list }, (draft) => {
      draft.list[0] = 2
      return draft
    })
    assert.notStrictEqual(rebuilt.list, list)
    assert.deepEqual(Object.getOwnPropertyDescriptor(rebuilt.list, 1), {
      configurable: true,
      enumerable: true,
      value: 2,
      writable: true,
    })
  })

  it("gives a getter's data property in a rebuilt object the getter's enumerability", () => {
    const target: Record<string, unknown> = { a: 1 }
    for (const [key, enumerable] of [
      ['hidden', false],
      ['shown', true],
    ] as const)
      Object.defineProperty(target, key, {
        configurable: true,
        enumerable,
        get(this: { a: number }) {
          return this.a
        },
      })
    const result = produce({ target }, (draft) => {
      draft.target.a = 2
      return draft
    })
    assert.notStrictEqual(result.target, target)
    assert.deepEqual(Object.getOwnPropertyDescriptor(result.target, 'hidden'), {
      configurable: true,
      enumerable: false,
      value: 2,
      writable: true,
    })
    assert.deepEqual(Object.keys(result.target), ['a', 'shown'])
  })
})

describe('private fields stay with the instance that declares them', () => {
  class Counter {
    readonly #count = 1
    label = 'a'
    get count(): number {
      return this.#count
    }
  }

  it('throws when a getter that uses a private field runs on a draft or a copy', () => {
    const counter = new Counter()
    assert.throws(() => produce({ counter }, (draft) => draft.counter.count), TypeError)
    assert.throws(() => (snapshot({ counter }) as { counter: Counter }).counter.count, TypeError)
    // An unchanged instance is kept, so its private field still works in the result.
    const result = produce({ counter, other: 0 }, (draft) => {
      draft.other = 1
      return draft
    })
    assert.strictEqual(result.counter, counter)
    assert.equal(result.counter.count, 1)
  })
})
