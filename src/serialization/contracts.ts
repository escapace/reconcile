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
  // Whether any of each shape's keys is a key `Object.prototype` holds; unread while measuring.
  shapeInherits: boolean[]
  shapes: number[]
  // Each shape's key words.
  shapeWords: number[]
  urls: number
  // Each node's words per occurrence (a bigint's digits; 0 otherwise), created by the first
  // bigint under a finite limit, so that documents without bigints read no weights.
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
  owners: Map<number, number> | undefined
  payloads: Array<Row | undefined>
  plain: number[][] | undefined
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
export type Leaf = (value: object, context: EncodeContext, kind?: number) => Row
export type Row = unknown[]
