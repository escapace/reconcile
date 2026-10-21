import type { Atom, Edge, NodeEdge } from '../types'

/** Distinguishes a canonical node reference from an atom edge without a string key check. */
export const isNode = <R extends { readonly node: number }>(edge: Edge<R>): edge is R =>
  (edge as NodeEdge).node !== undefined

/** A snapshot edge's value: a node's initialized target, or an atom's value. */
export const snapshotValue = (edge: Edge): unknown =>
  isNode(edge) ? (edge as { readonly target?: object } & NodeEdge).target : edge.value

/**
 * The snapshot walk calls a node's writer as a method of the node's private reference, so a
 * built-in writer can read the target from `this` instead of closing over it.
 */
export interface SnapshotReceiver {
  readonly layout?: object
  readonly target?: object
}

const missing: Atom = /* @__PURE__ */ Object.freeze({ node: undefined, value: undefined })

/** The edge at `index`, or an `undefined` atom past the end: never an element `Array.prototype`
 * supplies. */
export const edgeAt = (edges: readonly Edge[], index: number): Edge =>
  index < edges.length ? edges[index] : missing
