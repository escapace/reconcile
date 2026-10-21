import { assert, it, vi } from 'vitest'
import { builtinModules, builtinTypes, publicationTypes, snapshotTypes } from '../types/builtins'
import { TEMPORAL_KIND } from '../types/temporal'
import { OBJECT_KIND } from '../types/object'

it('preserves generic predicate traces, prefix stops and thrown errors', () => {
  const values = [
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
  ]
  const failure = new Error('prototype observation')
  for (const value of values) {
    for (const kind of [
      undefined,
      ...builtinModules.map((module) => module.kind),
      Symbol('unknown'),
    ]) {
      for (const throwAt of [0, 1, 3, 8]) {
        const run = (registry: Pick<typeof publicationTypes, 'matches' | 'recognize'>) => {
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
                kind === undefined
                  ? registry.recognize(candidate)
                  : registry.matches(kind, candidate),
              trace,
            }
          } catch (error) {
            return { error, trace }
          }
        }
        assert.deepEqual(run(publicationTypes), run(builtinTypes))
      }
    }
  }
})

it('preserves live Temporal property and hasInstance calls for hits and throws', () => {
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
          return { result: registry.recognize({}), trace }
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
