import { expect, it } from 'vitest'
import { normalize } from '../types/shared/collection'

it('keeps first key order and last values under SameValueZero normalization', () => {
  expect(
    normalize(
      [
        { node: undefined, value: -0 },
        { node: undefined, value: 'first' },
        { node: undefined, value: Number.NaN },
        { node: undefined, value: 1 },
        { node: undefined, value: +0 },
        { node: undefined, value: 'last' },
        { node: undefined, value: Number.NaN },
        { node: undefined, value: 2 },
      ],
      2,
    ),
  ).toEqual([
    { node: undefined, value: 0 },
    { node: undefined, value: 'last' },
    { node: undefined, value: Number.NaN },
    { node: undefined, value: 2 },
  ])
})

it('preserves canonical node references and distinct object-key identity', () => {
  const left = { node: 1 }
  const right = { node: 2 }
  const result = normalize(
    [
      left,
      { node: undefined, value: 1 },
      right,
      { node: undefined, value: 2 },
      left,
      { node: undefined, value: 3 },
    ],
    2,
  )
  expect(result).toEqual([
    left,
    { node: undefined, value: 3 },
    right,
    { node: undefined, value: 2 },
  ])
  expect(result[0]).toBe(left)
  expect(result[2]).toBe(right)
})

it('normalizes Set slots without losing symbols or canonical references', () => {
  const symbol = Symbol('member')
  const reference = { node: 1 }
  expect(
    normalize(
      [
        { node: undefined, value: -0 },
        { node: undefined, value: +0 },
        { node: undefined, value: symbol },
        reference,
        reference,
      ],
      1,
    ),
  ).toEqual([{ node: undefined, value: 0 }, { node: undefined, value: symbol }, reference])
})
