import type { Atom, Edge, NodeEdge, Primitive } from '../types'

/** Distinguishes a canonical node reference from an atom edge without a string key check. */
export const isNode = <R extends { readonly node: number }>(edge: Edge<R>): edge is R =>
  typeof edge === 'object' && edge !== null && (edge as NodeEdge).node !== undefined

/** An atom edge's value: a primitive is its own edge, an object atom is wrapped. */
export const atomValue = (edge: Atom | Primitive): unknown =>
  typeof edge === 'object' && edge !== null ? edge.value : edge

/** A snapshot edge's value: a node's initialized target, or an atom's value. */
export const snapshotValue = (edge: Edge): unknown =>
  isNode(edge) ? (edge as { readonly target?: object } & NodeEdge).target : atomValue(edge)

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
