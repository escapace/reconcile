import { describe, expect, it } from 'vitest'
import { isReconcileError, produce, reconcile } from '../index'

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
