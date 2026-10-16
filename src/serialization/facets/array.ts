import { decodeFail as fail, int, maxArrayLength } from '../common'
import type { Decoder, Row } from '../contracts'
function allocate(row: Row): unknown[] {
  const length = row[1]
  if (
    !int(length, maxArrayLength) ||
    (row[0] === 2 && row.length !== length + 2) ||
    (row[0] === 3 && row.length % 2 !== 0)
  )
    fail('array shape')
  return new Array<unknown>(length)
}
export const denseArray: Decoder = {
  allocate,
  fill(row, value, context) {
    const array = value as unknown[]
    for (let index = 2; index < row.length; index++) array[index - 2] = context.read(row[index])
  },
}
export const sparseArray: Decoder = {
  allocate,
  fill(row, value, context) {
    const array = value as unknown[]
    let previous = -1
    for (let index_ = 2; index_ < row.length; index_ += 2) {
      const index = row[index_]
      if (!int(index, (row[1] as number) - 1) || index <= previous) fail('sparse index')
      previous = index
      array[index] = context.read(row[index_ + 1])
    }
  },
}
