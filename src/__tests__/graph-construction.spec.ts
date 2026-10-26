import { expect, it } from 'vitest'
import { constructionOrder } from '../graph/construction'

it('allocates shells before views in captured order, including retained backing stores', () => {
  expect(constructionOrder([[3], [], [1], []], [false, true, false, false])).toEqual([3, 0, 2])
})
