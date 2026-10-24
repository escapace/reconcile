import type { RadixNode } from './radix'
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
  // The node the last `node` call found for an object that shares it with another view of its
  // storage, such as a Vue proxy and its raw object, or -1.
  alias: number
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
  // How far `heldTwice` has scanned each Map or Set frame that holds such a shared node; created on
  // the first.
  scans: Map<Frame, KeyScan> | undefined
  scratch: number[]
  shapeRoot: RadixNode<string>
  shapes: string[][]
  stack: Frame[]
  top: number
  // The objects whose node another view of their storage shares, such as a Vue proxy and its raw
  // object; created on the first.
  views: Set<object> | undefined
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
  // Whether `iterator` is a fresh native Map iterator, whose entries are read by index.
  keys: string[]
  length: number
  mapValue: unknown
  native: boolean
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
  // Whether `value` is a wrapper, such as a Vue reactive proxy, as `node` probed it.
  wrapped: boolean
  detail?: number
  next: (...arguments_: unknown[]) => unknown
  // The built-in step of a fresh native iterator, called with the iterator; undefined otherwise.
  step: ((iterator: object) => unknown) | undefined
}
/** The reference keys or members a frame's row holds before `scanned`, and where the scan of the
 * frame's runs stands. */
export interface KeyScan {
  boundary: number
  readonly held: Set<unknown>
  reference: boolean
  scanned: number
}
export type Leaf = (value: object, context: EncodeContext, kind?: number) => Row
export type Row = unknown[]
