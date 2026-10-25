import { assert, it } from 'vitest'
import { produce, reconcile, snapshot } from '../index'

/** A proxy over `target` that logs its prototype reads and writes under `name`. */
function counted<T extends object>(name: string, target: T, log: string[]): T {
  return new Proxy(target, {
    defineProperty(object, key, descriptor) {
      log.push(`${name} write`)
      return Reflect.defineProperty(object, key, descriptor)
    },
    getPrototypeOf(object) {
      log.push(`${name} prototype`)
      return Reflect.getPrototypeOf(object)
    },
    set(object, key, value, receiver) {
      log.push(`${name} write`)
      return Reflect.set(object, key, value, receiver)
    },
  })
}

/** The prototype reads each object received before the first write. */
function beforeWrite(log: readonly string[]): Record<string, number> {
  const first = log.findIndex((entry) => entry.endsWith(' write'))
  const reads: Record<string, number> = {}
  for (const entry of first === -1 ? log : log.slice(0, first))
    if (entry.endsWith(' prototype')) {
      const name = entry.slice(0, -' prototype'.length)
      reads[name] = (reads[name] ?? 0) + 1
    }
  return reads
}

it('reads each object prototype once before reconcile writes', () => {
  const log: string[] = []
  const current = counted('current', { u: counted('currentU', { n: 0 }, log) }, log)
  const next = counted('next', { u: counted('nextU', { n: 1 }, log) }, log)
  reconcile(current, next)
  assert.deepEqual(beforeWrite(log), { current: 1, currentU: 1, next: 1, nextU: 1 })
})

it('reads the prototype of a current object discovery meets at a second position once', () => {
  const log: string[] = []
  // `next` holds one object at both keys; `current` holds `alias` at the second, where discovery
  // recognizes it as a candidate of that object's node.
  const alias = counted('alias', { n: 0 }, log)
  const shared = { n: 1 }
  reconcile({ a: { n: 0 }, b: alias }, { a: shared, b: shared })
  assert.deepEqual(beforeWrite(log), { alias: 1 })
})

it('reads a draft base prototype once when the recipe begins', () => {
  const log: string[] = []
  produce(counted('base', { a: 0 }, log), (draft) => {
    log.push('recipe write')
    draft.a = 1
    return draft
  })
  assert.deepEqual(beforeWrite(log), { base: 1 })
})

it('reads each snapshot source prototype once', () => {
  const log: string[] = []
  snapshot(counted('source', { map: new Map(), u: counted('inner', { n: 0 }, log) }, log))
  assert.deepEqual(beforeWrite(log), { inner: 1, source: 1 })
})
