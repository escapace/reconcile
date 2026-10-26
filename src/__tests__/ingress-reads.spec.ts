import { assert, it } from 'vitest'
import { produce, reconcile, serialize, snapshot } from '../index'

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

it('reads the prototype of a current object aligned with two nodes once before reconcile writes', () => {
  const log: string[] = []
  // Both nodes of `next` align with `shared`; the second takes what the first recognized.
  const shared = counted('shared', { n: 0 }, log)
  reconcile({ a: shared, b: shared }, { a: { n: 1 }, b: { n: 2 } })
  assert.deepEqual(beforeWrite(log), { shared: 1 })
})

it('reads the prototype of a current object capture and discovery meet at two nodes once', () => {
  const log: string[] = []
  // Capture aligns `other` with the node of `c`; discovery meets it again at the node `a` and `b`
  // share, and takes the kind and prototype capture found.
  const other = counted('other', { n: 0 }, log)
  const shared = { n: 1 }
  reconcile({ a: { n: 0 }, b: other, c: other }, { a: shared, b: shared, c: { n: 2 } })
  assert.deepEqual(beforeWrite(log), { other: 1 })
})

/** Installs a global Temporal namespace of eight classes that logs the global's and each class's
 * reads in `trace`, and returns a value of its `PlainDate`. Each class copies a value through its
 * `from`, and its prototype holds the brand getter `temporalFrom` calls, the `toString` that
 * `serialize` calls and the `equals` that readback calls. */
function temporalNamespace(trace: string[]): object {
  const namespace = {}
  let plainDate: object | undefined
  for (const name of [
    'Duration',
    'Instant',
    'PlainDate',
    'PlainDateTime',
    'PlainMonthDay',
    'PlainTime',
    'PlainYearMonth',
    'ZonedDateTime',
  ]) {
    const Constructor = class {
      static from(): object {
        return Object.create(Constructor.prototype) as object
      }

      equals(): boolean {
        return this instanceof Constructor
      }

      toString(): string {
        return this instanceof Constructor ? '2020-01-01' : ''
      }
    }
    const prototype: object = Constructor.prototype
    const brand =
      name === 'Duration'
        ? 'sign'
        : name === 'Instant'
          ? 'epochMilliseconds'
          : name === 'PlainTime'
            ? 'hour'
            : 'monthCode'
    Object.defineProperty(prototype, brand, { get: () => 0 })
    Object.defineProperty(namespace, name, {
      get() {
        trace.push(`${name}:get`)
        return Constructor
      },
    })
    if (name === 'PlainDate') plainDate = Object.create(prototype) as object
  }
  Object.defineProperty(globalThis, 'Temporal', {
    configurable: true,
    get() {
      trace.push('Temporal:get')
      return namespace
    },
  })
  return plainDate!
}

it('reads the Temporal namespace for a value once, when recognition finds its class', () => {
  const recognition = ['Temporal:get', 'Duration:get', 'Instant:get', 'PlainDate:get']
  try {
    const trace: string[] = []
    snapshot({ value: temporalNamespace(trace) })
    assert.deepEqual(trace, recognition, 'snapshot')
    trace.length = 0
    const current = new Proxy(
      {},
      {
        defineProperty(target, key, descriptor) {
          trace.push('write')
          return Reflect.defineProperty(target, key, descriptor)
        },
        set(target, key, value) {
          trace.push('write')
          return Reflect.set(target, key, value)
        },
      },
    )
    reconcile(current, { value: temporalNamespace(trace) })
    // Readback recognizes the new copy again, after the write.
    assert.deepEqual(trace, [...recognition, 'write', ...recognition], 'reconcile')
    trace.length = 0
    produce({ value: temporalNamespace(trace) }, (draft) => {
      void draft.value
      assert.deepEqual(trace, recognition, 'produce')
      return draft
    })
    trace.length = 0
    // `serialize` recognizes a standard prototype, in its own class order.
    serialize({ value: temporalNamespace(trace) })
    assert.deepEqual(trace, ['Temporal:get', 'Instant:get', 'PlainDate:get'], 'serialize')
  } finally {
    Reflect.deleteProperty(globalThis, 'Temporal')
  }
})
