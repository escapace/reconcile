import type { DecodeContext } from './contracts'
import { decoders } from './facets/decode'
import { int, decodeFail as fail } from './common'
const specials = [undefined, NaN, Infinity, -Infinity, -0]
export function decodeGraph(text: string): unknown {
  if (typeof text !== 'string') fail('text')
  const document: unknown = JSON.parse(text)
  if (
    !Array.isArray(document) ||
    document.length !== 3 ||
    !Array.isArray(document[1]) ||
    !Array.isArray(document[2])
  )
    fail('envelope')
  const nodes = document[2] as unknown[][]
  const shapes = document[1] as unknown[]
  const output = new Array<unknown>(nodes.length)
  const context: DecodeContext = {
    checkedShapes: new Set(),
    nodes,
    output,
    owners: new Set(),
    read,
    shapes,
  }
  function read(token: unknown): unknown {
    if (token === null || typeof token === 'string' || typeof token === 'boolean') return token
    if (typeof token === 'number' && Number.isFinite(token) && !Object.is(token, -0)) {
      if (token >= 0) return token
      const id = -token - 6
      if (int(id, nodes.length - 1)) return output[id]
      const special = -token - 1
      if (int(special, 4)) return specials[special]
      fail('reference')
    }
    return readScalar(token)
  }

  for (let index = 0; index < nodes.length; index++) {
    const row = nodes[index]
    if (!Array.isArray(row) || !int(row[0], decoders.length - 1)) fail('node kind')
    output[index] = decoders[row[0]].allocate(row, context)
  }
  for (let index = 0; index < nodes.length; index++) {
    const row = nodes[index]
    const link = decoders[row[0] as number].link
    if (link !== undefined) {
      const value = link(row, context)
      if (value !== undefined) output[index] = value
    }
  }
  for (let index = 0; index < nodes.length; index++) {
    const row = nodes[index]
    decoders[row[0] as number].fill?.(row, output[index], context)
  }
  return read(document[0])
}

function readScalar(token: unknown): unknown {
  if (!Array.isArray(token)) fail('token')
  if (
    token.length === 2 &&
    token[0] === -7 &&
    typeof token[1] === 'number' &&
    Number.isFinite(token[1]) &&
    token[1] < 0
  )
    return token[1]
  if (
    token.length === 2 &&
    token[0] === -6 &&
    typeof token[1] === 'string' &&
    /^-?(?:0|[1-9]\d*)$/.exec(token[1]) !== null
  )
    return BigInt(token[1])
  fail('token')
}
