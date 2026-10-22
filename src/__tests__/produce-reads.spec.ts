import { assert, it } from 'vitest'
import { produce } from '../index'

const TRAPS = ['get', 'getOwnPropertyDescriptor', 'ownKeys', 'getPrototypeOf'] as const

/** A proxy over `target` that counts its read traps, by trap and key, under `name`. */
function counted<T extends object>(name: string, target: T, counts: Map<string, number>): T {
  const handler: ProxyHandler<T> = {}
  for (const trap of TRAPS)
    (handler as Record<string, unknown>)[trap] = (...parameters: unknown[]) => {
      const property = parameters[1]
      const key =
        typeof property === 'string' ? property : typeof property === 'symbol' ? 'symbol' : ''
      const entry = `${name}.${trap}(${key})`
      counts.set(entry, (counts.get(entry) ?? 0) + 1)
      return (Reflect[trap] as (...values: unknown[]) => unknown)(...parameters)
    }
  return new Proxy(target, handler)
}

it('reads each fact of an unchanged subtree once while keeping it', () => {
  const counts = new Map<string, number>()
  const inner = counted('inner', { y: 1 }, counts)
  const deep = counted('deep', { x: inner }, counts)
  const result = produce({ counter: 0, deep }, (draft) => {
    draft.counter += 1
    return draft
  })
  assert.strictEqual(result.deep, deep)
  // One key list (names, then symbols), one descriptor and value per key, one prototype, and the
  // Vue marker's own descriptor and read.
  for (const [name, key] of [
    ['deep', 'x'],
    ['inner', 'y'],
  ]) {
    assert.equal(counts.get(`${name}.ownKeys()`), 2, `${name} keys`)
    assert.equal(counts.get(`${name}.getOwnPropertyDescriptor(${key})`), 1, `${name} descriptor`)
    assert.equal(counts.get(`${name}.get(${key})`), 1, `${name} value`)
    assert.equal(counts.get(`${name}.getPrototypeOf()`), 1, `${name} prototype`)
  }
})

it('reads the written key once before the first copy', () => {
  const counts = new Map<string, number>()
  let beforeFinalization = new Map<string, number>()
  produce(counted('root', { a: 0, b: 1 }, counts), (draft) => {
    draft.a = 1
    beforeFinalization = new Map(counts)
    return draft
  })
  assert.equal(beforeFinalization.get('root.getOwnPropertyDescriptor(a)'), 1)
  assert.equal(beforeFinalization.get('root.get(a)'), 1)
  assert.equal(beforeFinalization.get('root.getOwnPropertyDescriptor(b)'), 1)
  assert.equal(beforeFinalization.get('root.get(b)'), 1)
})
