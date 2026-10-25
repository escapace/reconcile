import { assert, describe, it, vi } from 'vitest'

import { produce } from '../produce'
import { reconcile } from '../reconcile'
import { serialize } from '../serialize'
import { snapshot } from '../snapshot'
import { decodeText, encodeText } from './fixtures/text-codec'

interface TemporalConstructor {
  new (...arguments_: unknown[]): TemporalValue
  from: (input: unknown) => TemporalValue
}
interface TemporalValue {
  toString: (options?: { calendarName: string }) => string
}
const temporal = Reflect.get(globalThis, 'Temporal') as unknown as
  Record<string, TemporalConstructor> | undefined
const fixtures = [
  ['Duration', { milliseconds: 1000 }, { seconds: 2 }],
  ['Instant', '2025-01-02T03:04:05.123456789Z', '2026-01-02T03:04Z'],
  ['PlainDate', '2025-01-02', '2026-01-02'],
  ['PlainDateTime', '2025-01-02T03:04:05.123456789', '2026-01-02T03:04'],
  ['PlainMonthDay', '02-29', '03-01'],
  ['PlainTime', '03:04:05.123456789', '04:05'],
  ['PlainYearMonth', '2025-01', '2026-01'],
  ['ZonedDateTime', '2025-01-02T03:04:05.123456789+00:00[UTC]', '2026-01-02T03:04+00:00[UTC]'],
] as const

// Native Temporal is optional. On the experimental Node runtime, run this file with
// --config vitest.config.neutral.ts --execArgv=--harmony-temporal.
describe.skipIf(temporal === undefined)('Temporal values', () => {
  for (const [name, input, changed] of fixtures) {
    it(`${name} snapshots preserve aliases and distinct equal objects`, () => {
      const constructor = temporal![name]
      const first = constructor.from(input)
      const second = constructor.from(input)
      const source = { again: first, first, map: new Map([[first, second]]), second }
      const result = snapshot(source) as typeof source
      assert.notStrictEqual(result.first, first)
      assert.notStrictEqual(result.second, second)
      assert.notStrictEqual(result.first, result.second)
      assert.strictEqual(result.first, result.again)
      assert.strictEqual(result.map.get(result.first), result.second)
      assert.strictEqual(
        result.first.toString({ calendarName: 'always' }),
        first.toString({ calendarName: 'always' }),
      )
      if (name === 'Duration') {
        assert.strictEqual(Reflect.get(result.first, 'seconds'), 0)
        assert.strictEqual(Reflect.get(result.first, 'milliseconds'), 1000)
      }
    })

    it(`${name} serializes with its class, exact value and aliases`, () => {
      const constructor = temporal![name]
      const first = constructor.from(input)
      const source = { again: first, first, second: constructor.from(input) }
      const result = decodeText(encodeText(source)) as typeof source
      assert.strictEqual(result.first, result.again)
      assert.notStrictEqual(result.first, result.second)
      assert.strictEqual(Object.getPrototypeOf(result.first), constructor.prototype)
      assert.strictEqual(
        result.first.toString({ calendarName: 'always' }),
        first.toString({ calendarName: 'always' }),
      )
      if (name === 'Duration') {
        assert.strictEqual(Reflect.get(result.first, 'seconds'), 0)
        assert.strictEqual(Reflect.get(result.first, 'milliseconds'), 1000)
      }
    })

    it(`${name} drafts reuse unchanged copies and retain new identities`, () => {
      const constructor = temporal![name]
      const value = constructor.from(input)
      const base = { value }
      assert.strictEqual(
        produce(base, (draft) => {
          draft.value.toString()
          return draft
        }),
        base,
      )
      const replacement = constructor.from(input)
      const result = produce(base, (draft) => {
        draft.value = replacement
        return draft
      })
      assert.notStrictEqual(result.value, value)
      assert.strictEqual(result.value.toString(), replacement.toString())
      assert.strictEqual(base.value, value)
    })

    it(`${name} reconciles equal roots and replaces changed nested values`, () => {
      const constructor = temporal![name]
      const value = constructor.from(input)
      assert.strictEqual(reconcile(value, constructor.from(input)), value)
      assert.throws(() => reconcile(value, constructor.from(changed)))
      const base = { value }
      const next = { value: constructor.from(changed) }
      assert.strictEqual(reconcile(base, next), base)
      assert.notStrictEqual(base.value, value)
      assert.notStrictEqual(base.value, next.value)
      assert.strictEqual(base.value.toString(), next.value.toString())
    })
  }

  it('does not merge Duration component distributions with identical strings', () => {
    const milliseconds = temporal!.Duration.from({ milliseconds: 1000 })
    const seconds = temporal!.Duration.from({ seconds: 1 })
    assert.strictEqual(milliseconds.toString(), seconds.toString())
    assert.throws(() => reconcile(milliseconds, seconds))
    const base = { value: milliseconds }
    reconcile(base, { value: seconds })
    assert.strictEqual(Reflect.get(base.value, 'seconds'), 1)
    assert.strictEqual(Reflect.get(base.value, 'milliseconds'), 0)
  })

  it('does not conflate different Temporal classes', () => {
    assert.throws(() =>
      reconcile(temporal!.PlainDate.from('2025-01-02'), temporal!.PlainDateTime.from('2025-01-02')),
    )
  })

  it('does not conflate equal instants in different time zones', () => {
    const utc = temporal!.ZonedDateTime.from('2025-01-02T00:00+00:00[UTC]')
    const offset = temporal!.ZonedDateTime.from('2025-01-02T01:00+01:00[+01:00]')
    assert.throws(() => reconcile(utc, offset))
  })
})

it('works without an installed Temporal namespace', () => {
  vi.stubGlobal('Temporal', undefined)
  try {
    const value = { date: new Date(0), integer: 123n }
    const copy = snapshot(value) as typeof value
    assert.strictEqual(copy.integer, 123n)
    assert.strictEqual(copy.date.getTime(), 0)
    assert.notStrictEqual(copy.date, value.date)
  } finally {
    vi.unstubAllGlobals()
  }
})

describe.skipIf(temporal === undefined)('Temporal native representation', () => {
  it('recognizes a namespace installed after an earlier operation', () => {
    vi.stubGlobal('Temporal', undefined)
    try {
      snapshot({ ordinary: true })
      vi.stubGlobal('Temporal', temporal)
      const value = temporal!.Instant.from('2025-01-01T00:00Z')
      const copy = snapshot(value) as typeof value
      assert.notStrictEqual(copy, value)
      assert.strictEqual(copy.toString(), value.toString())
    } finally {
      vi.unstubAllGlobals()
    }
  })

  for (const [name, arguments_, other] of [
    ['PlainMonthDay', [2, 29, 'iso8601', 2000], [2, 29, 'iso8601', 2004]],
    ['PlainYearMonth', [2025, 2, 'iso8601', 13], [2025, 2, 'iso8601', 14]],
    ['PlainDate', [2025, 2, 13, 'iso8601'], [2025, 2, 13, 'gregory']],
  ] as const) {
    it(`${name} retains calendar and reference date distinctions`, () => {
      const first = new temporal![name](...arguments_)
      const second = new temporal![name](...other)
      const copy = snapshot(first) as typeof first
      assert.strictEqual(
        copy.toString({ calendarName: 'always' }),
        first.toString({ calendarName: 'always' }),
      )
      assert.throws(() => reconcile(first, second))
      const state = { value: first }
      reconcile(state, { value: second })
      assert.strictEqual(
        state.value.toString({ calendarName: 'always' }),
        second.toString({ calendarName: 'always' }),
      )
    })
  }
})

describe.skipIf(temporal === undefined)('Temporal recipe methods and subclasses', () => {
  it('assigns immutable method results without changing the recipe input', () => {
    interface PlainDateValue extends TemporalValue {
      add: (duration: { days: number }) => PlainDateValue
      with: (fields: { day: number }) => PlainDateValue
    }
    const value = temporal!.PlainDate.from('2025-01-02') as PlainDateValue
    const base = { value }
    const added = produce(base, (draft) => {
      draft.value = draft.value.add({ days: 2 })
      return draft
    })
    assert.strictEqual(added.value.toString(), '2025-01-04')
    const replaced = produce(base, (draft) => {
      draft.value = draft.value.with({ day: 20 })
      return draft
    })
    assert.strictEqual(replaced.value.toString(), '2025-01-20')
    assert.strictEqual(base.value, value)
    assert.strictEqual(value.toString(), '2025-01-02')
    assert.strictEqual(
      produce(base, (draft) => {
        draft.value.add({ days: 2 })
        draft.value.with({ day: 20 })
        return draft
      }),
      base,
    )
  })

  it('keeps the subclass in fresh copies and omits extra properties', () => {
    class CustomDate extends temporal!.PlainDate {
      extra = { ignored: true }
    }
    const value = new CustomDate(2025, 1, 2)
    // A copy keeps its source's prototype, as for every built-in subclass. Compare prototypes with
    // `===`: an assertion message would format the prototype and call its getters.
    const copy = snapshot(value) as TemporalValue
    assert.isTrue(Object.getPrototypeOf(copy) === CustomDate.prototype)
    assert.strictEqual(Object.hasOwn(copy, 'extra'), false)
    assert.strictEqual(copy.toString(), '2025-01-02')
    const base = { value: temporal!.PlainDate.from('2024-01-01') }
    reconcile(base, { value })
    assert.isTrue(Object.getPrototypeOf(base.value) === CustomDate.prototype)
    assert.strictEqual(Object.hasOwn(base.value, 'extra'), false)
    assert.strictEqual(base.value.toString(), value.toString())
    assert.deepEqual(value.extra, { ignored: true })
  })
})

describe.skipIf(temporal === undefined)('Temporal native slot equality', () => {
  it('ignores own Duration component shadows during equality', () => {
    const value = temporal!.Duration.from({ seconds: 1 })
    Object.defineProperty(value, 'seconds', { value: 2 })
    assert.throws(() => reconcile(value, temporal!.Duration.from({ seconds: 2 })))
    assert.strictEqual(reconcile(value, temporal!.Duration.from({ seconds: 1 })), value)
    const base = { value }
    assert.strictEqual(
      produce(base, (draft) => {
        draft.value.toString()
        return draft
      }),
      base,
    )
    const copy = snapshot(value) as TemporalValue
    assert.strictEqual(Reflect.get(copy, 'seconds'), 1)
    assert.strictEqual(Object.hasOwn(copy, 'seconds'), false)
  })

  it('ignores subclass Duration component overrides during equality', () => {
    class CustomDuration extends temporal!.Duration {
      // eslint-disable-next-line typescript/class-literal-property-style -- Exercise an inherited getter shadow, separately from an own field.
      get seconds() {
        return 2
      }
    }
    const value = new CustomDuration(0, 0, 0, 0, 0, 0, 1)
    assert.throws(() => reconcile(value, temporal!.Duration.from({ seconds: 2 })))
    assert.strictEqual(reconcile(value, temporal!.Duration.from({ seconds: 1 })), value)
  })
})

describe.skipIf(temporal === undefined)('Temporal classes and Symbol.hasInstance', () => {
  it('recognizes and compares a value by its prototype chain, not by Symbol.hasInstance', () => {
    const PlainDate = temporal!.PlainDate
    const date = PlainDate.from('2025-01-02')
    Object.defineProperty(PlainDate, Symbol.hasInstance, { configurable: true, value: () => false })
    try {
      const copy = snapshot({ date }) as { date: TemporalValue }
      assert.notStrictEqual(copy.date, date)
      assert.strictEqual(copy.date.toString(), '2025-01-02')
      const current = { date }
      assert.strictEqual(reconcile(current, { date: PlainDate.from('2025-01-02') }).date, date)
      const result = produce({ date }, (draft) => ({ copied: draft.date }))
      assert.strictEqual(result.copied.toString(), '2025-01-02')
    } finally {
      Reflect.deleteProperty(PlainDate, Symbol.hasInstance)
    }
  })
})

describe.skipIf(temporal === undefined)('objects that only inherit a Temporal prototype', () => {
  it("throw the class's native TypeError in every function without having a property read", () => {
    for (const [name, input] of fixtures) {
      const reads: PropertyKey[] = []
      const fake = new Proxy(Object.create(temporal![name].prototype as object) as object, {
        get(target, key, receiver) {
          reads.push(key)
          return Reflect.get(target, key, receiver) as unknown
        },
      })
      for (const run of [
        () => snapshot(fake),
        () => serialize(fake),
        () => reconcile({ value: 1 }, { value: fake }),
        () => reconcile({ value: temporal![name].from(input) }, { value: fake }),
        () => produce({ value: fake }, (draft) => ({ copy: draft.value })),
      ])
        assert.throws(run, TypeError)
      assert.deepEqual(reads, [])
    }
  })
})
