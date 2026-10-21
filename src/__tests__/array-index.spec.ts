import { expect, it } from 'vitest'
import fc from 'fast-check'
import { arrayIndex } from '../object-property'

it('classifies keys consistently with native array length updates', () => {
  fc.assert(
    fc.property(
      fc.oneof(
        fc.string(),
        fc.double().map(String),
        fc.integer({ max: 4_294_967_305, min: -10 }).map(String),
        fc.constantFrom('', '-0', '01', '+1', '1.0', '1e0', '4294967295', '4294967296'),
      ),
      (key) => {
        const array: unknown[] = []
        if (key !== 'length') Object.defineProperty(array, key, { value: true })
        expect(arrayIndex(key)).toBe(array.length === 0 ? undefined : array.length - 1)
      },
    ),
    { numRuns: 5000, seed: 20_260_908 },
  )
})

it('excludes symbols and numeric inputs without coercion', () => {
  expect(arrayIndex(Symbol('0'))).toBeUndefined()
  expect(arrayIndex(0)).toBeUndefined()
})

it('handles decimal boundaries and rejects non-ASCII or alternate spellings', () => {
  expect(arrayIndex('4294967294')).toBe(4_294_967_294)
  for (const key of [
    '4294967295',
    '4294967296',
    '9999999999',
    '10000000000',
    '-0',
    '01',
    '+1',
    '1e0',
    '1.0',
    ' 1',
    '1\u00a0',
    '\u0661',
    '\ud800',
    '\0',
    '9'.repeat(4096),
  ]) {
    expect(arrayIndex(key)).toBeUndefined()
  }
})

it('does not inspect or coerce non-string objects', () => {
  let observations = 0
  const input = {
    get length() {
      observations += 1
      return 1
    },
    [Symbol.toPrimitive]() {
      observations += 1
      return '0'
    },
  }
  expect(Reflect.apply(arrayIndex, undefined, [input])).toBeUndefined()
  expect(observations).toBe(0)
})

it('agrees with native array indices on every short string over a numeric alphabet', () => {
  const alphabet = ['', '0', '1', '9', '-', '+', 'e', '.', 'a', ' ', '٠']
  const array: unknown[] = []
  for (const a of alphabet)
    for (const b of alphabet)
      for (const c of alphabet) {
        const key = a + b + c
        array.length = 0
        if (key !== 'length') Object.defineProperty(array, key, { configurable: true, value: true })
        expect(arrayIndex(key)).toBe(array.length === 0 ? undefined : array.length - 1)
      }
})
