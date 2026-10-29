import { describe, expect, it } from 'vitest'
import { deserialize, isReconcileError, requiredMaxBytes, serialize } from '../index'

// Size.lean, independently of the decoder: words of the decoded value, with every object stored
// once and every primitive charged where it occurs. A view's buffer and a URL's own parameters
// are reachable objects too.
const text = (length: number) => Math.ceil(length / 4)
const hexWords = (value: bigint) =>
  Math.ceil((value < 0n ? -value : value).toString(16).length / 16)

function words(root: unknown): number {
  const seen = new Set<object>()
  const pending: object[] = []
  const occurrence: Occurrence = (value) => {
    if (typeof value === 'string') return text(value.length)
    if (typeof value === 'bigint') return hexWords(value)
    if (value !== null && typeof value === 'object' && !seen.has(value)) {
      seen.add(value)
      pending.push(value)
    }
    return 0
  }
  let total = 1 + occurrence(root)
  while (pending.length !== 0) total += 1 + objectWords(pending.pop()!, occurrence)
  return total
}

type Occurrence = (value: unknown) => number

// An object's own words after its header: its slots and their primitives, or its contents.
function objectWords(value: object, occurrence: Occurrence): number {
  return (
    collectionWords(value, occurrence) ??
    nativeWords(value, occurrence) ??
    recordWords(value, occurrence)
  )
}

function collectionWords(value: object, occurrence: Occurrence): number | undefined {
  let total = 0
  if (Array.isArray(value)) for (const item of value) total += 1 + occurrence(item)
  else if (value instanceof Map)
    for (const [key, item] of value) total += 2 + occurrence(key) + occurrence(item)
  else if (value instanceof Set) for (const member of value) total += 1 + occurrence(member)
  else return undefined
  return total
}

function nativeWords(value: object, occurrence: Occurrence): number | undefined {
  if (value instanceof Date) return 1
  if (value instanceof ArrayBuffer) return Math.ceil(value.byteLength / 8)
  if (ArrayBuffer.isView(value)) return Math.ceil(value.byteLength / 8) + occurrence(value.buffer)
  if (value instanceof URL) return text(value.href.length) + occurrence(value.searchParams)
  if (value instanceof URLSearchParams) {
    let total = 0
    for (const [name, item] of value) total += 2 + text(name.length) + text(item.length)
    return total
  }
  return undefined
}

function recordWords(value: object, occurrence: Occurrence): number {
  let total = 0
  for (const key of Object.keys(value))
    total += 2 + text(key.length) + occurrence((value as Record<string, unknown>)[key])
  return total
}

const roundTrip = (value: unknown, maxBytes: number) =>
  deserialize(JSON.parse(JSON.stringify(serialize(value))), { maxBytes })

function causeOf(run: () => unknown): unknown {
  try {
    run()
  } catch (error) {
    return isReconcileError(error) ? error.cause : error
  }
  return undefined
}

function fixtures(): Array<[string, unknown]> {
  const shared = { label: 'shared' }
  const cycle: Record<string, unknown> = { name: 'node' }
  cycle.self = cycle
  const buffer = new ArrayBuffer(64)
  const big = 2n ** 300n + 1n
  const sparse: unknown[] = []
  sparse[1000] = 'end'
  const key = 'k'.repeat(100)
  return [
    ['a number', 1],
    ['a string', 'abcdefghi'],
    ['an empty object', {}],
    ['an empty array', []],
    ['a record', { a: 1, bb: 'two', ccc: [true, null] }],
    ['a null-prototype record', Object.assign(Object.create(null) as object, { z: 'zz' })],
    ['shared objects', { left: shared, list: [shared, shared], right: shared }],
    ['a cycle', cycle],
    ['a sparse array', sparse],
    ['records sharing a long key', Array.from({ length: 50 }, (_, n) => ({ [key]: n }))],
    ['repeated bigints', [big, big, -big, 0n, 1n, big]],
    ['a bigint root', -big],
    ['undefined and special numbers', [undefined, NaN, Infinity, -Infinity, -0]],
    [
      'a Map and a Set',
      {
        map: new Map<unknown, unknown>([
          ['k', shared],
          [shared, 2n],
        ]),
        set: new Set([1, shared, 'x']),
      },
    ],
    ['a Date', [new Date(5), new Date(Number.NaN)]],
    [
      'overlapping views',
      {
        buffer,
        views: [new Uint8Array(buffer), new Float64Array(buffer), new DataView(buffer, 8, 16)],
      },
    ],
    ['a lone view', new Uint16Array([1, 2, 3])],
    ['URLs', [new URL('https://example.com/a?x=1&y=two'), new URLSearchParams('a=1&b=22')]],
  ]
}

describe('deserialize maxBytes', () => {
  it.each(fixtures())(
    'accepts %s at exactly eight bytes per word, not one byte less',
    (_, value) => {
      const size = words(value)
      expect(() => roundTrip(value, 8 * size)).not.toThrow()
      expect(() => roundTrip(value, 8 * size + 7)).not.toThrow()
      expect(causeOf(() => roundTrip(value, 8 * size - 1))).toEqual({
        maxBytes: 8 * size - 1,
        type: 'DeserializeLimitExceeded',
      })
    },
  )

  it('charges repeated keys, bigints and overlapping views at every occurrence', () => {
    const key = 'k'.repeat(1000)
    const records = Array.from({ length: 100 }, () => ({ [key]: 1 }))
    // The key is written once but held by every record: 250 words each.
    expect(words(records)).toBeGreaterThan(100 * 250)
    expect(causeOf(() => roundTrip(records, 8 * 100 * 250))).toMatchObject({
      type: 'DeserializeLimitExceeded',
    })
    const big = 2n ** 4000n
    expect(
      causeOf(() =>
        roundTrip(
          Array.from({ length: 100 }, () => big),
          8 * 100 * 60,
        ),
      ),
    ).toMatchObject({
      type: 'DeserializeLimitExceeded',
    })
    const buffer = new ArrayBuffer(8000)
    const views = Array.from({ length: 50 }, () => new Uint8Array(buffer))
    expect(causeOf(() => roundTrip(views, 8 * 50 * 1000))).toMatchObject({
      type: 'DeserializeLimitExceeded',
    })
  })

  it('rejects a declared sparse length before allocating it', () => {
    const document = [[0, 0, 1, 3], [[4_294_967_295, [0], []]]]
    expect(JSON.stringify(document).length).toBeLessThan(45)
    const start = performance.now()
    expect(causeOf(() => deserialize(document, { maxBytes: 1_000_000 }))).toEqual({
      maxBytes: 1_000_000,
      type: 'DeserializeLimitExceeded',
    })
    expect(performance.now() - start).toBeLessThan(50)
  })

  it('rejects a document with more nodes than words before reading its tables', () => {
    // A thousand nodes whose control table is invalid: the node count decides first.
    const document = [
      Array.from({ length: 1001 }, () => -1),
      Array.from({ length: 1000 }, () => []),
    ]
    expect(causeOf(() => deserialize(document, { maxBytes: 8 * 999 }))).toMatchObject({
      type: 'DeserializeLimitExceeded',
    })
    expect(causeOf(() => deserialize(document, { maxBytes: Infinity }))).toMatchObject({
      type: 'DeserializeInputInvalid',
    })
  })

  it('charges literals the encoder never writes, and stops on a cyclic one', () => {
    const literal = { a: [1, 'wxyz'], b: 'xy' }
    const document = [[0, 0, 1, 2], [[structuredClone(literal)]]]
    const size = words([literal])
    expect(() => deserialize(structuredClone(document), { maxBytes: 8 * size })).not.toThrow()
    expect(
      causeOf(() => deserialize(structuredClone(document), { maxBytes: 8 * size - 1 })),
    ).toMatchObject({
      type: 'DeserializeLimitExceeded',
    })
    const cyclic: Record<string, unknown> = {}
    cyclic.self = cyclic
    expect(
      causeOf(() => deserialize([[0, 0, 1, 2], [[cyclic]]], { maxBytes: 8000 })),
    ).toMatchObject({
      type: 'DeserializeLimitExceeded',
    })
    expect(causeOf(() => deserialize([cyclic], { maxBytes: 8000 }))).toMatchObject({
      type: 'DeserializeLimitExceeded',
    })
  })

  it('writes no array twice and none shared with another call', () => {
    const document = serialize([undefined, NaN, Infinity, -Infinity, -0, undefined]) as unknown[][]
    const arrays = [document, ...document, ...document[1]] as unknown[]
    expect(new Set(arrays).size).toBe(arrays.length)
    const other = serialize(undefined) as unknown[][]
    expect(other[1][0]).not.toBe(document[1][1])
    for (const row of document[1]) expect(Object.isFrozen(row)).toBe(false)
  })

  const temporal = Reflect.get(globalThis, 'Temporal') as unknown as
    | Record<string, { from: (text: string) => { toString: () => string } }>
    | undefined
  it.skipIf(temporal === undefined)('charges a Temporal value by the text it holds', () => {
    // A shorter accepted form is charged as the longer text the value holds.
    const value = temporal!.ZonedDateTime.from('2020-01-01T00:00[UTC]')
    const size = 1 + 1 + Math.ceil(value.toString().length / 4)
    expect(requiredMaxBytes(serialize(value), { maxBytes: Infinity })).toBe(8 * size)
    expect(() => roundTrip(value, 8 * size)).not.toThrow()
    expect(causeOf(() => roundTrip(value, 8 * size - 1))).toMatchObject({
      type: 'DeserializeLimitExceeded',
    })
    const duration = temporal!.Duration.from('P1D')
    expect(() => roundTrip(duration, 8 * 12)).not.toThrow()
    expect(causeOf(() => roundTrip(duration, 8 * 12 - 1))).toMatchObject({
      type: 'DeserializeLimitExceeded',
    })
  })

  it('rejects literals that are not JSON data before reading them', () => {
    const literals: unknown[] = [
      new Uint8Array(20_000_000),
      new Map([[1, 2]]),
      Object.create(null),
      10n ** 1000n,
      () => 1,
      undefined,
      Symbol('x'),
    ]
    for (const literal of literals) {
      const start = performance.now()
      expect(causeOf(() => deserialize([[0, 0, 1, 2], [[literal]]], { maxBytes: 64_000 }))).toEqual(
        {
          reason: 'literal',
          type: 'DeserializeInputInvalid',
        },
      )
      expect(causeOf(() => deserialize([[{ nested: literal }]], { maxBytes: 64_000 }))).toEqual({
        reason: 'literal',
        type: 'DeserializeInputInvalid',
      })
      expect(performance.now() - start).toBeLessThan(50)
    }
    // With no limit, literals are not read: trusted callers pass data as they built it.
    expect(deserialize([[0, 0, 1, 2], [[undefined]]], { maxBytes: Infinity })).toEqual([undefined])
  })

  it('checks a reference before charging the bigint it names', () => {
    // At 32 bytes, charging an unchecked 'length' (2 words) would exceed the limit first.
    for (const reference of ['length', 'constructor', -1, 2, 1.5])
      expect(
        causeOf(() =>
          deserialize(
            [
              [0, 1, 0, 2, 2, 0, 1, 18],
              [[reference], ['0x1']],
            ],
            { maxBytes: 32 },
          ),
        ),
      ).toEqual({ reason: 'reference', type: 'DeserializeInputInvalid' })
  })

  it('charges values JSON cannot write by the table, not by their JSON text', () => {
    // JSON.stringify writes each of these as {} or omits the property; their size is larger.
    for (const value of [{ a: undefined }, new Map([[1, 2]]), new Set([1, 2, 3])]) {
      const size = words(value)
      expect(8 * size).toBeGreaterThan(8 * JSON.stringify(value).length)
      expect(() => roundTrip(value, 8 * size)).not.toThrow()
    }
  })

  it('charges repeated Map keys as written, at least their decoded size', () => {
    // Two pairs with the key 0x0 fold into one entry; both pairs are charged.
    const document = [
      [0, 1, 0, 5, 4, 0, 1, 1, 1, 1, 18],
      [[1, 1, 1, 2], ['0x0']],
    ]
    const value = deserialize(structuredClone(document), { maxBytes: Infinity })
    expect([...(value as Map<unknown, unknown>)]).toEqual([[0n, 2]])
    expect(
      causeOf(() => deserialize(structuredClone(document), { maxBytes: 8 * words(value) })),
    ).toMatchObject({
      type: 'DeserializeLimitExceeded',
    })
  })

  it('accepts every JSON value within eight bytes per character of its JSON text', () => {
    let seed = 3
    const random = () => (seed = (seed * 1_103_515_245 + 12_345) % 2 ** 31) / 2 ** 31
    const generate = (depth: number): unknown => {
      const pick = random()
      if (depth > 4 || pick < 0.3)
        return [0, 7, -1.5e300, 'é😀"\\\n', true, null, '', 'abcd'][Math.floor(random() * 8)]
      if (pick < 0.65)
        return Array.from({ length: Math.floor(random() * 5) }, () => generate(depth + 1))
      return Object.fromEntries(
        Array.from({ length: Math.floor(random() * 5) }, (_, index) => [
          ['', 'k', 'ключ', '😀'][Math.floor(random() * 4)] + index,
          generate(depth + 1),
        ]),
      )
    }
    for (let index = 0; index < 2000; index++) {
      const value = generate(0)
      const size = words(value)
      expect(8 * size).toBeLessThanOrEqual(8 * JSON.stringify(value).length)
      expect(() => roundTrip(value, 8 * JSON.stringify(value).length)).not.toThrow()
    }
  })
})

const measure = (json: unknown) => requiredMaxBytes(json, { maxBytes: Infinity })

// n sparse arrays of the largest length: 2 + n + n * 2 ** 32 words.
const largeDocument = (n: number) => [
  [0, ...Array.from({ length: n }, () => 1), 0, 2, 2, 0, 1, 3],
  [
    Array.from({ length: n }, (_, index) => index + 1),
    ...Array.from({ length: n }, () => [2 ** 32 - 1, [1], [1]]),
  ],
]

describe('requiredMaxBytes', () => {
  it.each(fixtures())('measures %s as eight bytes per word, without modifying it', (_, value) => {
    for (const json of [
      serialize(value),
      JSON.parse(JSON.stringify(serialize(value))) as unknown,
    ]) {
      const before = structuredClone(json)
      const maxBytes = measure(json)
      expect(maxBytes).toBe(8 * words(value))
      expect(json).toStrictEqual(before)
      expect(() => deserialize(structuredClone(json), { maxBytes })).not.toThrow()
      expect(causeOf(() => deserialize(json, { maxBytes: maxBytes - 1 }))).toMatchObject({
        type: 'DeserializeLimitExceeded',
      })
    }
  })

  it('measures what deserialize charges, more than the value when Map keys fold', () => {
    const document = [
      [0, 1, 0, 5, 4, 0, 1, 1, 1, 1, 18],
      [[1, 1, 1, 2], ['0x0']],
    ]
    const maxBytes = measure(document)
    const value = deserialize(structuredClone(document), { maxBytes })
    expect(maxBytes).toBeGreaterThan(8 * words(value))
    expect(causeOf(() => deserialize(document, { maxBytes: maxBytes - 1 }))).toMatchObject({
      type: 'DeserializeLimitExceeded',
    })
  })

  it('measures literals the encoder never writes', () => {
    const literal = { a: [1, 'wxyz'], b: 'xy' }
    expect(measure([[0, 0, 1, 2], [[literal]]])).toBe(8 * words([literal]))
    expect(measure([literal])).toBe(8 * words(literal))
  })

  it('returns Infinity when no finite maxBytes is large enough', () => {
    const largest = 2 ** 18 - 1
    expect(measure(largeDocument(largest))).toBe(8 * (2 + largest + largest * 2 ** 32))
    expect(measure(largeDocument(largest + 1))).toBe(Infinity)
    expect(
      causeOf(() => deserialize(largeDocument(largest + 1), { maxBytes: Number.MAX_SAFE_INTEGER })),
    ).toMatchObject({ type: 'DeserializeLimitExceeded' })
  })

  it('stops at maxBytes and rejects what deserialize rejects under a finite limit', () => {
    const json = serialize({ name: 'Ada', tags: ['a', 'b'] })
    const maxBytes = measure(json)
    expect(requiredMaxBytes(json, { maxBytes })).toBe(maxBytes)
    expect(causeOf(() => requiredMaxBytes(json, { maxBytes: maxBytes - 1 }))).toEqual({
      maxBytes: maxBytes - 1,
      type: 'DeserializeLimitExceeded',
    })
    const invalids: unknown[] = [-1, 1.5, NaN, undefined]
    for (const invalid of invalids)
      expect(causeOf(() => requiredMaxBytes(json, { maxBytes: invalid as number }))).toEqual({
        maxBytes: invalid,
        type: 'DeserializeLimitInvalid',
      })
    expect(causeOf(() => measure({}))).toMatchObject({ type: 'DeserializeInputInvalid' })
    expect(causeOf(() => measure([[0, 0, 1, 2], [[new Map()]]]))).toEqual({
      reason: 'literal',
      type: 'DeserializeInputInvalid',
    })
  })

  it('accepts and rejects the base64 that deserialize does', () => {
    for (const text of ['AQID', 'AAA*', 'AA=A', 'AAA ', 'AQ==', 'A===', 'AQ=A', 'AA-_']) {
      const document = [[0, 0, 1, 7], [[text]]]
      const cause = causeOf(() => deserialize(structuredClone(document), { maxBytes: 64 }))
      expect(causeOf(() => requiredMaxBytes(document, { maxBytes: 64 }))).toEqual(cause)
    }
    expect(measure([[0, 0, 1, 7], [['AQID']]])).toBe(8 * (1 + 1 + 1))
  })

  it('reads maxBytes once', () => {
    let reads = 0
    const options = {
      get maxBytes() {
        reads++
        return Infinity
      },
    }
    requiredMaxBytes(serialize([1]), options)
    expect(reads).toBe(1)
  })
})
