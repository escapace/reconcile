import type { Edge, NodeEdge } from '../types'

/** Distinguishes a canonical node reference from an atom edge without a string key check. */
export const isNode = <R extends { readonly node: number }>(edge: Edge<R>): edge is R =>
  (edge as NodeEdge).node !== undefined
