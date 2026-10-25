import { describe, expect, it } from 'vitest'
import { deserialize, isReconcileError, produce, reconcile, serialize, snapshot } from '../index'

/** The traps `reconcile` calls on a proxied `current` holding `key`, with the key renamed. */
function traps(key: string): string[] {
  const log: string[] = []
  const current = new Proxy<Record<string, unknown>>(
    { a: 1, [key]: 1 },
    {
      getOwnPropertyDescriptor(target, property) {
        log.push(property === key ? 'descriptor key' : `descriptor ${String(property)}`)
        return Reflect.getOwnPropertyDescriptor(target, property)
      },
      has(target, property) {
        log.push(property === key ? 'has key' : `has ${String(property)}`)
        return Reflect.has(target, property)
      },
    },
  )
  reconcile(current, { a: 2, [key]: 2 })
  return log
}

// The same reconcile with an ordinary key in the same place observes the same traps.
describe('reconcile and keys a standard prototype holds', () => {
  it('asks current nothing more for a key that Object.prototype holds as data', () => {
    expect(traps('toString')).toEqual(traps('ordinary'))
  })

  it('rejects a key reaching a setter beyond Array.prototype, as on Object.prototype', () => {
    let calls = 0
    const prototype = Object.create(Array.prototype) as object
    const holder = Object.create(prototype) as Record<string, unknown>
    // eslint-disable-next-line no-extend-native -- the test installs a setter on Object.prototype
    Object.defineProperty(Object.prototype, 'reconcileBoundaryKey', {
      configurable: true,
      get: () => undefined,
      set: () => {
        calls += 1
      },
    })
    let caught: unknown
    try {
      reconcile(holder, { reconcileBoundaryKey: 1 })
    } catch (error) {
      caught = error
    } finally {
      Reflect.deleteProperty(Object.prototype, 'reconcileBoundaryKey')
    }
    expect(isReconcileError(caught) && caught.cause.type).toBe('PublicationRejected')
    expect(calls).toBe(0)
  })
})

describe('a draft descriptor read that reenters the draft', () => {
  it('reports each property with its own attributes', () => {
    let draft: Record<string, unknown> | undefined
    const base = new Proxy<Record<string, unknown>>(
      Object.defineProperty({ a: 1 }, 'h', {
        configurable: true,
        enumerable: false,
        value: 2,
        writable: true,
      }),
      {
        get(target, key, receiver) {
          if (key === 'a' && draft !== undefined) Object.getOwnPropertyDescriptor(draft, 'h')
          return Reflect.get(target, key, receiver) as unknown
        },
      },
    )
    const descriptors = produce(base, (value) => {
      draft = value
      return { a: Object.getOwnPropertyDescriptor(value, 'a'), keys: Object.keys(value) }
    }) as { a: PropertyDescriptor; keys: string[] }
    expect(descriptors.a.enumerable).toBe(true)
    expect(descriptors.keys).toEqual(['a'])
  })
})

describe('produce and indices Array.prototype holds', () => {
  it('keeps a write to an array whose other slots are getters', () => {
    // Identity restoration looks up each getter slot's attributes by position; the tables have a
    // hole at every data slot, which must not reach the getter Array.prototype holds here.
    const base: unknown[] = []
    for (const index of [0, 1])
      Object.defineProperty(base, index, {
        configurable: true,
        enumerable: true,
        get: () => `getter ${index}`,
      })
    let reads = 0
    // eslint-disable-next-line no-extend-native -- the test installs an accessor on Array.prototype
    Object.defineProperty(Array.prototype, 0, {
      configurable: true,
      get() {
        reads += 1
        return 8
      },
      // An assignment through it defines the receiver's own element, as an ordinary one would.
      set(this: object, value: unknown) {
        Object.defineProperty(this, 0, {
          configurable: true,
          enumerable: true,
          value,
          writable: true,
        })
      },
    })
    try {
      const result = produce(base, (draft) => {
        Reflect.deleteProperty(draft, 0)
        draft[0] = 8
        return draft
      })
      expect(result).not.toBe(base)
      expect(Object.getOwnPropertyDescriptor(result, 0)).toEqual({
        configurable: true,
        enumerable: true,
        value: 8,
        writable: true,
      })
      expect(reads).toBe(0)
    } finally {
      Reflect.deleteProperty(Array.prototype, 0)
    }
  })
})

describe('a loop that application code or a rejection leaves', () => {
  const failure = new Error('thrown by application code')
  const throwing = {
    get a(): never {
      throw failure
    },
  }
  const hidden = Object.defineProperty({}, 'a', {
    enumerable: false,
    get(): never {
      throw failure
    },
  })
  const cases: Array<[string, () => unknown]> = [
    ['reconcile reading next', () => reconcile({ a: 1 }, throwing)],
    ['snapshot reading a hidden key', () => snapshot(hidden)],
    [
      'produce copying a proxy whose get trap throws',
      () =>
        produce(
          {
            p: new Proxy(
              { a: 1 },
              {
                get: () => {
                  throw failure
                },
              },
            ),
          },
          (draft) => {
            ;(draft.p as Record<string, unknown>).z = 1
          },
        ),
    ],
    [
      'produce finalizing an object whose getter throws',
      () =>
        produce({ x: 1 }, (draft) => {
          ;(draft as Record<string, unknown>).y = throwing
          return draft
        }),
    ],
    [
      'deserialize charging a literal past its limit',
      () => deserialize([{ a: 'x'.repeat(400) }], { maxBytes: 64 }),
    ],
    [
      'a Map draft forEach with a receiver',
      () =>
        produce(new Map([[1, 2]]), (draft) => {
          draft.forEach(() => undefined, {})
        }),
    ],
  ]

  it.each(cases)('reads no return through Object.prototype: %s', (_name, call) => {
    let reads = 0
    // eslint-disable-next-line no-extend-native -- the test counts reads of Object.prototype.return
    Object.defineProperty(Object.prototype, 'return', {
      configurable: true,
      get() {
        reads += 1
        return undefined
      },
    })
    try {
      call()
    } catch {
      // The error is the case's own; only the reads are checked here.
    } finally {
      Reflect.deleteProperty(Object.prototype, 'return')
    }
    expect(reads).toBe(0)
  })
})

describe('serialize left by a throw inside a Map or Set', () => {
  it('closes no built-in iterator and calls no return a prototype holds', () => {
    // The built-in iterators have no `return`; one planted on their shared prototype is not called.
    const iteratorPrototype = Object.getPrototypeOf(
      Object.getPrototypeOf(new Map().entries()),
    ) as object
    let calls = 0
    Object.defineProperty(iteratorPrototype, 'return', {
      configurable: true,
      value() {
        calls += 1
        return { done: true, value: undefined }
      },
    })
    const failure = new Error('thrown by a getter')
    const value = new Map([
      [
        1,
        {
          get a(): never {
            throw failure
          },
        },
      ],
    ])
    let caught: unknown
    try {
      serialize(value)
    } catch (error) {
      caught = error
    } finally {
      Reflect.deleteProperty(iteratorPrototype, 'return')
    }
    expect(caught).toBe(failure)
    expect(calls).toBe(0)
  })
})
