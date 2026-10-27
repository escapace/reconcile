import { sparseArray } from '../standard-prototypes'
// ShapeRadix.lean radix_eq_internAll: equal key sequences share one id, assigned in
// first-occurrence order as Positional.lean internAll assigns it; the proof is generic in the
// key type. Record shapes intern their
// property names and layouts their nonnegative integers.
// Path-compressed per-call trie node: the edge into it is keys[from..to) of the sequence that
// created it; children are keyed by the first key of their edge, in a Map for names and a sparse
// array for integers, detached from `Array.prototype` so a missing child reads as undefined.
// Lookups that succeed change nothing; a sequence that diverges or ends inside an edge splits it.
export interface RadixNode<K> {
  from: number
  id: number
  keys: K[]
  next: Array<RadixNode<K> | undefined> | Map<K, RadixNode<K>> | undefined
  to: number
}
export const radixTrie = <K>(): RadixNode<K> => ({
  from: 0,
  id: -1,
  keys: [],
  next: undefined,
  to: 0,
})
function adopt<K>(node: RadixNode<K>, key: K, value: RadixNode<K>): void {
  if (typeof key === 'number')
    ((node.next ??= sparseArray<RadixNode<K> | undefined>()) as Array<RadixNode<K> | undefined>)[
      key
    ] = value
  else ((node.next ??= new Map()) as Map<K, RadixNode<K>>).set(key, value)
}
function child<K>(node: RadixNode<K>, key: K): RadixNode<K> | undefined {
  const next = node.next
  if (next === undefined) return undefined
  return typeof key === 'number'
    ? (next as Array<RadixNode<K> | undefined>)[key]
    : (next as Map<K, RadixNode<K>>).get(key)
}
// ShapeRadix.lean getR: the id of keys[0 ..< length], or -1; changes nothing.
export function lookup<K>(root: RadixNode<K>, keys: K[], length: number): number {
  let node = root
  let index = 0
  while (index < length) {
    const next = child(node, keys[index])
    if (next === undefined) return -1
    for (let position = next.from; position < next.to; position++, index++)
      if (index === length || keys[index] !== next.keys[position]) return -1
    node = next
  }
  return node.id
}
// ShapeRadix.lean setR: returns the id of keys, appending keys itself to table when it is new.
export function intern<K>(root: RadixNode<K>, table: K[][], keys: K[]): number {
  let node = root
  let index = 0
  while (index < keys.length) {
    const next = child(node, keys[index])
    if (next === undefined) {
      const leaf = { from: index, id: table.length, keys, next: undefined, to: keys.length }
      adopt(node, keys[index], leaf)
      table.push(keys)
      return leaf.id
    }
    let position = next.from + 1
    index++
    while (position < next.to && index < keys.length && keys[index] === next.keys[position]) {
      position++
      index++
    }
    node = position === next.to ? next : split(node, next, position)
  }
  if (node.id < 0) {
    node.id = table.length
    table.push(keys)
  }
  return node.id
}
// Splits the edge into child at position; the returned middle node carries the prefix.
function split<K>(parent: RadixNode<K>, node: RadixNode<K>, position: number): RadixNode<K> {
  const middle: RadixNode<K> = {
    from: node.from,
    id: -1,
    keys: node.keys,
    next: undefined,
    to: position,
  }
  adopt(middle, node.keys[position], node)
  adopt(parent, node.keys[node.from], middle)
  node.from = position
  return middle
}
