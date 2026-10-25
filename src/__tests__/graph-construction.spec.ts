import { expect, it } from 'vitest'
import { constructionOrder } from '../graph/construction'

it('allocates shells before views in captured order, including retained backing stores', () => {
  expect(constructionOrder([[3], [], [1], []], [false, true, false, false])).toEqual([3, 0, 2])
})

it('supports several dependency layers and shared construction prerequisites', () => {
  expect(constructionOrder([[2, 3], [0], [3], []], [false, false, false, false])).toEqual([
    3, 2, 0, 1,
  ])
})

it('rejects fresh construction cycles while allowing cycles broken by retained identities', () => {
  expect(constructionOrder([[1], [0]], [false, false])).toBeUndefined()
  expect(constructionOrder([[1], [0]], [true, false])).toEqual([1])
  expect(constructionOrder([[0]], [true])).toEqual([])
  expect(constructionOrder([[0]], [false])).toBeUndefined()
})

it('counts duplicate dependencies while keeping allocation order independent of queue admission', () => {
  expect(constructionOrder([[3, 3], [2], [], []], [false, false, false, false])).toEqual([
    2, 3, 0, 1,
  ])
  expect(constructionOrder([[], [0, 0], []], [true, false, false])).toEqual([2, 1])
  expect(constructionOrder([[1, 1], [0]], [false, false])).toBeUndefined()
})
