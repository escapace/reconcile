import type { RadixNode } from './radix'
import type { Step } from '../standard-prototypes'
// The size limit in words (maxBytes / 8, rounded down) and the words charged so far.
export interface Budget {
  limit: number
  maxBytes: number
  words: number
}
export interface DecodeContext extends Budget {
  // The control table; layouts and shapes are read in place by the offset of their first entry.
  control: unknown[]
  cursor: number
  ends: number[]
  // Whether words are charged: under a finite limit, or when measuring. Otherwise, literals and
  // parameter entries are not read.
  limited: boolean
  // Measuring charges and checks as decoding does, but writes nothing into the document and
  // allocates no record, Map or Set.
  measuring: boolean
  nodeLayouts: number[]
  output: unknown[]
  owned: number
  parameters: Array<number | undefined> | undefined
  payloads: unknown[][]
  // Per shape: the offset of its first key, 1 when `Object.prototype` holds one of its keys
  // (unread while measuring) or 0, and its key words; shape `j`'s at `3 * j` to `3 * j + 2`
  // (Types.CallTables.interleave_get).
  shapes: number[]
  urls: number
  // Each node's words per occurrence (a bigint's digits; 0 otherwise), created by the first
  // bigint while sizes are charged, so that documents without bigints read no weights.
  weights: number[] | undefined
}
// A layout argument is the control offset of the layout's tag; its length precedes it.
export interface Decoder {
  fill:
    | ((
        payload: Row,
        value: unknown,
        layout: number,
        context: DecodeContext,
        index: number,
      ) => void)
    | undefined
  link:
    ((payload: Row, layout: number, context: DecodeContext, index: number) => unknown) | undefined
  allocate: (payload: Row, layout: number, context: DecodeContext, index: number) => unknown
}
export interface EncodeContext {
  bigints: Map<bigint, number> | undefined
  boundaries: number[]
  descriptors: number[]
  ids: Map<object, number>
  layoutRoot: RadixNode<number>
  layouts: number[][]
  payloads: Array<Row | undefined>
  plain: Array<number[] | undefined> | undefined
  scalars: number[] | undefined
  scratch: number[]
  shapeRoot: RadixNode<string>
  shapes: string[][]
  stack: Frame[]
  top: number
}
export interface Frame {
  child: unknown
  end: number
  holes: number[] | undefined
  id: number
  index: number
  input: number
  // A fresh native Map or Set iterator, stepped by `step`.
  iterator: object
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
  // The built-in step of `iterator`, called with it.
  step: Step
}
export type Leaf = (value: object, kind?: number) => Row
export type Row = unknown[]
