import { assert, describe, it } from 'vitest'
import { isReconcileError, produce, reconcile, serialize, snapshot } from '../index'

// Values whose state lives in internal slots are atoms, like functions: every function keeps
// them by reference and never drafts or copies them. lean/Types/Atoms.lean proves the
// classifier and check-atoms-runtime.ts compares it natively.

class HttpError extends Error {
  constructor(
    message: string,
    readonly status: number,
  ) {
    super(message)
  }
}

const serializeError = (value: unknown): string | undefined => {
  try {
    serialize(value)
    return undefined
  } catch (error) {
    return isReconcileError(error) ? error.cause.type : String(error)
  }
}

const atoms = (): Array<[string, object]> => [
  ['RegExp', /a/g],
  ['Error', new Error('boom')],
  ['Error subclass', new HttpError('missing', 404)],
  ['WeakMap', new WeakMap()],
  ['WeakSet', new WeakSet()],
  ['WeakRef', new WeakRef({})],
  ['FinalizationRegistry', new FinalizationRegistry(() => undefined)],
  ['Promise', Promise.resolve(1)],
  ['Number object', Object(1) as object],
  ['String object', Object('ab') as object],
  ['Boolean object', Object(true) as object],
  ['BigInt object', Object(1n) as object],
  ['Symbol object', Object(Symbol('s')) as object],
  ['Blob', new Blob(['a'])],
]

describe('values the library cannot copy are kept by reference', () => {
  for (const [name, value] of atoms()) {
    it(`snapshot, produce and reconcile keep a ${name}; serialize rejects it`, () => {
      assert.strictEqual((snapshot({ value }) as { value: object }).value, value)
      const current: Record<string, unknown> = { value: 0 }
      reconcile(current, { value })
      assert.strictEqual(current.value, value)
      const result = produce({ other: 0, value }, (draft) => {
        assert.strictEqual(draft.value, value)
        draft.other = 1
        return draft
      })
      assert.strictEqual(result.value, value)
      assert.equal(serializeError({ value }), 'SerializeValueUnsupported')
    })
  }

  it('reconcile takes the next RegExp instead of keeping the old pattern', () => {
    const current = { pattern: /a/ }
    const next = { pattern: /b/ }
    reconcile(current, next)
    assert.strictEqual(current.pattern, next.pattern)
  })

  it('reconcile takes the next WeakMap with its entries', () => {
    const key = {}
    const current = { cache: new WeakMap<object, number>() }
    const next = { cache: new WeakMap([[key, 1]]) }
    reconcile(current, next)
    assert.strictEqual(current.cache.get(key), 1)
  })

  it('reconcile replaces an error without rewriting the old one', () => {
    const old = new Error('first')
    const current = { error: old }
    const next = { error: new TypeError('second') }
    reconcile(current, next)
    assert.strictEqual(current.error, next.error)
    assert.equal(old.message, 'first')
  })

  it('reconcile keeps an equal reference and returns a different root as is', () => {
    const pattern = /a/
    const current = { pattern }
    reconcile(current, { pattern })
    assert.strictEqual(current.pattern, pattern)
    const next = /b/
    assert.strictEqual(reconcile(/a/, next), next)
  })

  it('produce keeps an unchanged error instead of copying it on every call', () => {
    const error = new Error('boom')
    const result = produce({ count: 0, error }, (draft) => {
      draft.count = 1
      return draft
    })
    assert.strictEqual(result.error, error)
  })

  it('a recipe can call RegExp, WeakMap and Promise methods', async () => {
    const key = {}
    const state = { cache: new WeakMap<object, number>(), pattern: /a/g, ready: Promise.resolve(2) }
    let value: Promise<number> | undefined
    produce(state, (draft) => {
      assert.ok(draft.pattern.test('a'))
      draft.cache.set(key, 1)
      value = draft.ready.then((n) => n * 2)
      return draft
    })
    assert.equal(await value, 4)
    // Atoms are not drafted, so a method that changes one changes the original.
    assert.equal(state.cache.get(key), 1)
    assert.equal(state.pattern.lastIndex, 1)
  })

  it('a copy keeps atoms as Map keys and Set members', () => {
    const pattern = /a/
    const copy = snapshot({ map: new Map([[pattern, 1]]), set: new Set([pattern]) }) as {
      map: Map<RegExp, number>
      set: Set<RegExp>
    }
    assert.equal(copy.map.get(pattern), 1)
    assert.ok(copy.set.has(pattern))
  })

  it('objects that inherit a listed prototype are atoms; plain and class objects are not', () => {
    const fake = Object.create(Error.prototype) as object
    assert.strictEqual((snapshot({ fake }) as { fake: object }).fake, fake)
    class Point {
      x = 1
    }
    const point = new Point()
    const copy = snapshot({ plain: { x: 1 }, point }) as { plain: object; point: Point }
    assert.notStrictEqual(copy.point, point)
    assert.ok(copy.point instanceof Point)
  })
})
