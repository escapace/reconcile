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

it('copies an object that reaches a change through a cycle back into the walk', () => {
  // `a` walks `b` first; `b` leans on `a`, still being walked, and `a` then finds its changed
  // child, so `b` needs a copy too.
  const b: { back: object | undefined } = { back: undefined }
  const a = { link: b, mark: { n: 0 } }
  b.back = a
  const result = produce({ x: a, y: b }, (draft) => {
    draft.x.mark.n = 1
    return draft
  })
  assert.notStrictEqual(result.x, a)
  assert.notStrictEqual(result.y, b)
  assert.strictEqual(result.y.back, result.x)
  assert.strictEqual(result.x.link, result.y)
})

it('reads an unchanged sibling of a change once', () => {
  const counts = new Map<string, number>()
  const sibling = counted('sibling', { n: 0 }, counts)
  produce({ sibling, target: { n: 0 } }, (draft) => {
    draft.target.n = 1
    return draft
  })
  assert.equal(counts.get('sibling.ownKeys()'), 2, 'one key list')
  assert.equal(counts.get('sibling.get(n)'), 1)
})

it('keeps an unchanged object the recipe inserts, reading it once', () => {
  const counts = new Map<string, number>()
  const inserted = counted('inserted', { n: 0 }, counts)
  const result = produce({ slot: undefined as object | undefined }, (draft) => {
    draft.slot = inserted
    return draft
  })
  assert.strictEqual(result.slot, inserted)
  assert.equal(counts.get('inserted.ownKeys()'), 2, 'one key list')
  assert.equal(counts.get('inserted.get(n)'), 1)
})
