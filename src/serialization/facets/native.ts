import { decodeFail as fail, int } from '../common'
import { decodedSize, decodeBytes } from '../binary'
import { decodeTemporal, constructView, viewConstructors, temporalNames } from '../native'
import type { Decoder } from '../contracts'
export const date: Decoder = {
  allocate(row) {
    const time = row[1]
    if (
      row.length !== 2 ||
      (time !== null &&
        (typeof time !== 'number' || !Number.isInteger(time) || !(Math.abs(time) <= 8.64e15)))
    )
      fail('date')
    return new Date(time ?? NaN)
  },
}
export const buffer: Decoder = {
  allocate(row) {
    if (row.length !== 2) fail('base64')
    const length = decodedSize(row[1])
    return decodeBytes(row[1] as string, length)
  },
}
export const view: Decoder = {
  allocate(row) {
    const kind = row[1]
    if (row.length !== 5 || !validViewKind(kind) || !int(row[3]) || !int(row[4])) fail('view')
  },
  link(row, context) {
    const reference = row[2]
    if (
      typeof reference !== 'number' ||
      !int(-reference - 6, context.nodes.length - 1) ||
      context.nodes[-reference - 6][0] !== 7
    )
      fail('view buffer')
    const kind = row[1] as number
    const length = row[4] as number
    const offset = row[3] as number
    const storage = context.output[-reference - 6] as ArrayBuffer
    const unit = kind === -1 ? 1 : viewConstructors[kind]!.BYTES_PER_ELEMENT
    if (
      offset % unit !== 0 ||
      offset > storage.byteLength ||
      length > Math.floor((storage.byteLength - offset) / unit)
    )
      fail('view bounds')
    return constructView(kind, storage, offset, length)
  },
}
export const url: Decoder = {
  allocate(row) {
    if (row.length !== 2 || typeof row[1] !== 'string') fail('URL')
    return new URL(row[1])
  },
}
export const parameters: Decoder = {
  allocate(row, context) {
    if (row.length !== 2) fail('params')
    if (typeof row[1] === 'string') return new URLSearchParams(row[1])
    if (!int(row[1], context.nodes.length - 1)) fail('params owner')
    return undefined
  },
  link(row, context) {
    if (typeof row[1] === 'string') return undefined
    const owner = row[1] as number
    if (context.nodes[owner][0] !== 9 || context.owners.has(owner)) fail('params owner')
    context.owners.add(owner)
    return (context.output[owner] as URL).searchParams
  },
}
export const temporal: Decoder = {
  allocate(row) {
    const kind = row[1]
    if (row.length !== 3 || !int(kind, temporalNames.length - 1)) fail('Temporal')
    const payload = row[2]
    if (kind === 7) {
      if (!Array.isArray(payload) || payload.length !== 10 || !payload.every(Number.isInteger))
        fail('duration')
    } else if (typeof payload !== 'string') fail('Temporal text')
    return decodeTemporal(kind, payload as string | number[])
  },
}

function validViewKind(kind: unknown): kind is number {
  return (
    typeof kind === 'number' &&
    Number.isInteger(kind) &&
    kind >= -1 &&
    kind < viewConstructors.length &&
    (kind === -1 || viewConstructors[kind] !== undefined)
  )
}
