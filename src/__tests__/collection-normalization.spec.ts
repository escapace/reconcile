import { expect, it } from 'vitest'
import { normalize } from '../types/shared/collection'

it('keeps first key order and last values under SameValueZero normalization', () => {
  expect(
    normalize(
      [
        { value: -0 },
        { value: 'first' },
        { value: Number.NaN },
        { value: 1 },
        { value: +0 },
        { value: 'last' },
        { value: Number.NaN },
        { value: 2 },
      ],
      2,
    ),
  ).toEqual([{ value: 0 }, { value: 'last' }, { value: Number.NaN }, { value: 2 }])
})

it('preserves canonical node references and distinct object-key identity', () => {
  const left = { node: 1 }
  const right = { node: 2 }
  const result = normalize([left, { value: 1 }, right, { value: 2 }, left, { value: 3 }], 2)
  expect(result).toEqual([left, { value: 3 }, right, { value: 2 }])
  expect(result[0]).toBe(left)
  expect(result[2]).toBe(right)
})

it('normalizes Set slots without losing symbols or canonical references', () => {
  const symbol = Symbol('member')
  const reference = { node: 1 }
  expect(
    normalize([{ value: -0 }, { value: +0 }, { value: symbol }, reference, reference], 1),
  ).toEqual([{ value: 0 }, { value: symbol }, reference])
})
