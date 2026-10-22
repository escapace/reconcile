import { assert, it } from 'vitest'
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
