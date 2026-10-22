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
 * Prototype reads of the object by the built-in registries: the array probe and checks that stop
 * at it, or name no kind, read nothing, as the generic scan does; any other check reads the object
 * once, where the generic scan reads it once per `instanceof` probe.
 */
function expectedReads(value: object, kind: symbol | undefined, generic: number): number {
  if (Array.isArray(value) || kind === ARRAY_KIND) return generic
  return kind !== undefined && !builtinModules.some((module) => module.kind === kind) ? generic : 1
}

it("reads the object once and keeps the generic scan's results and errors", () => {
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

it('decides Temporal classes by their prototypes, reading each live class in order', () => {
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
  // The pre-unrolling loop is an independent oracle for the generic registry, which still asks
  // each constructor's `Symbol.hasInstance`.
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
        const prototypes: object[] = []
        for (const [index, name] of names.entries()) {
          function Constructor() {
            return index
          }
          prototypes.push(Constructor.prototype as object)
          Object.defineProperty(Constructor, Symbol.hasInstance, {
            value() {
              trace.push(`${name}:instance`)
              return index === stop
            },
          })
          Object.defineProperty(namespace, name, {
            get() {
              assert.strictEqual(this, namespace)
              trace.push(`${name}:get`)
              if (index === stop && throws) throw failure
              return Constructor
            },
          })
        }
        const value = stop < 0 ? custom() : (Object.create(prototypes[stop]) as object)
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
          return { result: registry.recognize(value), trace }
        } catch (error) {
          return { error, trace }
        } finally {
          vi.unstubAllGlobals()
        }
      }
      assert.deepEqual(run(builtinTypes), run(reference))
      // The built-in registries read the namespace and each class up to the match, and never
      // call `Symbol.hasInstance`.
      const reads = [
        'Temporal:get',
        ...names.slice(0, stop < 0 ? names.length : stop + 1).map((name) => `${name}:get`),
      ]
      assert.deepEqual(
        run(snapshotTypes),
        throws && stop >= 0
          ? { error: failure, trace: reads }
          : { result: stop < 0 ? OBJECT_KIND : TEMPORAL_KIND, trace: reads },
      )
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
