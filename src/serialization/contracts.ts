import type { RadixNode } from './radix'
export interface DecodeContext {
  bigints: Set<string> | undefined
  cursor: number
  ends: number[]
  layouts: number[][]
  nodeLayouts: number[][]
  output: unknown[]
  owned: number
  parameters: number[] | undefined
  payloads: unknown[][]
  scalars: number
  shapes: string[][]
  urls: number
}
export interface Decoder {
  allocate: (payload: Row, layout: number[], context: DecodeContext) => unknown
  fill?: (
    payload: Row,
    value: unknown,
    layout: number[],
    context: DecodeContext,
    index: number,
  ) => void
  link?: (payload: Row, layout: number[], context: DecodeContext, index: number) => unknown
}
export interface EncodeContext {
  bigints: Map<bigint, number> | undefined
  boundaries: number[]
  descriptors: number[]
  hasBuffers: boolean
  ids: Map<object, number>
  layoutRoot: RadixNode<number>
  layouts: number[][]
  owners: Map<number, number> | undefined
  payloads: Array<Row | undefined>
  scalars: number[] | undefined
  scratch: number[]
  shapeRoot: RadixNode<string>
  shapes: string[][]
  stack: Frame[]
  top: number
}
export interface Frame {
  active: boolean
  child: unknown
  end: number
  holes: number[] | undefined
  id: number
  index: number
  input: number
  iterator: { next: unknown; return?: unknown }
  keys: string[]
  length: number
  mapValue: unknown
  phase: number
  reference: boolean
  row: Row
  runs: number
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
