import { assert, it, vi } from 'vitest'
import { builtinModules, builtinTypes, publicationTypes, snapshotTypes } from '../types/builtins'
import { TEMPORAL_KIND } from '../types/temporal'
import { OBJECT_KIND } from '../types/object'
import { ARRAY_KIND } from '../types/array'

/** An instance of a class recognition does not know. */
const custom = (): object => Object.create({ kind: 'custom' }) as object

const values = (): object[] => [
  {},
  [],
  new Date(),
  new Map(),
  new Set(),
  new ArrayBuffer(4),
  new DataView(new ArrayBuffer(4)),
  new Uint8Array(4),
  new URL('https://example.test/'),
  new URLSearchParams('a=1'),
  /a/,
  new TypeError('atom'),
  Object.create(null) as object,
  custom(),
]

/** Recognizes or checks one kind on a proxy that records its prototype reads and fails the read
 * at `throwAt`. */
function observe(
  registry: Pick<typeof publicationTypes, 'matches' | 'recognize'>,
  value: object,
  kind: symbol | undefined,
  throwAt: number,
  failure: Error,
) {
  const trace: string[] = []
  const candidate = new Proxy(value, {
    getPrototypeOf(target) {
      trace.push('prototype')
      if (trace.length === throwAt) throw failure
      return Reflect.getPrototypeOf(target)
    },
  })
  try {
    return {
      result:
        kind === undefined ? registry.recognize(candidate) : registry.matches(kind, candidate),
      trace,
    }
  } catch (error) {
    return { error, trace }
  }
}

/**
 * Prototype reads of the built-in registries: the array probe and checks that stop at it, or name
 * no kind, read nothing; past them a plain object takes one read, and any other object one read
 * before the generic scan, which then makes `generic` reads with the same result.
 */
function expectedReads(value: object, kind: symbol | undefined, generic: number): number {
  if (Array.isArray(value) || kind === ARRAY_KIND) return generic
  if (kind !== undefined && !builtinModules.some((module) => module.kind === kind)) return generic
  const first = Object.getPrototypeOf(value) as object | null
  return first === null || first === Object.prototype ? 1 : generic + 1
}

it('decides a plain object by one prototype read and keeps the generic scan otherwise', () => {
  const failure = new Error('prototype observation')
  const kinds = [undefined, ...builtinModules.map((module) => module.kind), Symbol('unknown')]
  for (const value of values())
    for (const kind of kinds) {
      const generic = observe(builtinTypes, value, kind, 0, failure)
      const read = observe(publicationTypes, value, kind, 0, failure)
      assert.deepEqual(read, {
        ...generic,
        trace: Array.from(
          { length: expectedReads(value, kind, generic.trace.length) },
          () => 'prototype',
        ),
      })
      // A failing first read propagates its error, as the scan's first read does.
      const failed = observe(publicationTypes, value, kind, 1, failure)
      const reference = observe(builtinTypes, value, kind, 1, failure)
      assert.strictEqual(failed.error, reference.error)
      assert.strictEqual(failed.result, reference.result)
    }
})

it('recognizes a typed array by its brand whatever its prototype', () => {
  for (const prototype of [Object.prototype, null, Map.prototype, Date.prototype]) {
    const view = Object.setPrototypeOf(new Uint8Array(1), prototype) as object
    assert.strictEqual(publicationTypes.recognize(view), builtinTypes.recognize(view))
  }
})

it('preserves live Temporal property and hasInstance calls for objects that are not plain', () => {
  const names = [
    'Duration',
    'Instant',
    'PlainDate',
    'PlainDateTime',
    'PlainMonthDay',
    'PlainTime',
    'PlainYearMonth',
    'ZonedDateTime',
  ]
  const failure = new Error('native recognition')
  // The pre-unrolling loop is an independent oracle for native constructor observations.
  const reference = {
    recognize(value: object): symbol {
      const namespace = Reflect.get(globalThis, 'Temporal') as Record<string, unknown>
      for (const name of names) {
        const constructor = namespace[name]
        if (typeof constructor === 'function' && value instanceof constructor) return TEMPORAL_KIND
      }
      return OBJECT_KIND
    },
  }
  for (const stop of [-1, 0, 4, 7]) {
    for (const throws of [false, true]) {
      const run = (registry: Pick<typeof snapshotTypes, 'recognize'>) => {
        const trace: string[] = []
        const namespace = {}
        for (const [index, name] of names.entries()) {
          function Constructor() {
            return index
          }
          Object.defineProperty(Constructor, Symbol.hasInstance, {
            value() {
              trace.push(`${name}:instance`)
              if (index === stop && throws) throw failure
              return index === stop
            },
          })
          Object.defineProperty(namespace, name, {
            get() {
              assert.strictEqual(this, namespace)
              trace.push(`${name}:get`)
              return Constructor
            },
          })
        }
        vi.stubGlobal('Temporal', namespace)
        Object.defineProperty(globalThis, 'Temporal', {
          configurable: true,
          get() {
            assert.strictEqual(this, globalThis)
            trace.push('Temporal:get')
            return namespace
          },
        })
        try {
          return { result: registry.recognize(custom()), trace }
        } catch (error) {
          return { error, trace }
        } finally {
          vi.unstubAllGlobals()
        }
      }
      assert.deepEqual(run(snapshotTypes), run(builtinTypes))
      assert.deepEqual(run(snapshotTypes), run(reference))
    }
  }
})

it('reads no Temporal namespace for a plain object', () => {
  const trace: string[] = []
  Object.defineProperty(globalThis, 'Temporal', {
    configurable: true,
    get() {
      trace.push('Temporal:get')
      return {}
    },
  })
  try {
    assert.strictEqual(snapshotTypes.recognize({}), OBJECT_KIND)
    assert.strictEqual(snapshotTypes.recognize(Object.create(null) as object), OBJECT_KIND)
    assert.deepEqual(trace, [])
  } finally {
    Reflect.deleteProperty(globalThis, 'Temporal')
  }
})
