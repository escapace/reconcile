export interface DecodeContext {
  checkedShapes: Set<number>
  nodes: Row[]
  output: unknown[]
  owners: Set<number>
  shapes: unknown[]
  read: (token: unknown) => unknown
}
export interface Decoder {
  allocate: (row: Row, context: DecodeContext) => unknown
  fill?: (row: Row, value: unknown, context: DecodeContext) => void
  link?: (row: Row, context: DecodeContext) => unknown
}
export interface EncodeContext {
  hasBuffers: boolean
  ids: Map<object, number>
  owner: (parameters: number, owner: number) => void
  shape: (keys: string[]) => number
}
export interface Frame {
  active: boolean
  child: unknown
  count: number
  dense: boolean
  entries: unknown[]
  id: number
  index: number
  input: unknown
  iterator: { next: unknown; return?: unknown }
  keys: string[]
  length: number
  mapValue: unknown
  phase: number
  row: Row
  state: {
    buffer: ArrayBuffer
    byteOffset: number
    href: string
    length: number
    parameters: URLSearchParams
  }
  tag: number
  value: object
  detail?: number
  next: (...arguments_: unknown[]) => unknown
}
export type Leaf = (value: object, context: EncodeContext, kind?: number) => Row
export type Row = unknown[]
