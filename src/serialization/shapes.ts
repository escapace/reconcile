// ShapeRadix.lean radix_matches_signature: equal key sequences share one id, assigned in
// first-occurrence order, exactly as the previous JSON.stringify(keys) memo did.
// Path-compressed per-call trie node: the edge into it is keys[from..to) of the shape that
// created it; children are keyed by the first key of their edge. Lookups that succeed change
// nothing; a shape that diverges or ends inside an edge splits it.
export interface ShapeNode {
  from: number
  id: number
  keys: string[]
  next: Map<string, ShapeNode> | undefined
  to: number
}
export const shapeTrie = (): ShapeNode => ({ from: 0, id: -1, keys: [], next: undefined, to: 0 })
export function internShape(root: ShapeNode, shapes: string[][], keys: string[]): number {
  let node = root
  let index = 0
  while (index < keys.length) {
    const child = node.next?.get(keys[index])
    if (child === undefined) {
      const leaf = { from: index, id: shapes.length, keys, next: undefined, to: keys.length }
      ;(node.next ??= new Map()).set(keys[index], leaf)
      shapes.push(keys)
      return leaf.id
    }
    let position = child.from + 1
    index++
    while (position < child.to && index < keys.length && keys[index] === child.keys[position]) {
      position++
      index++
    }
    node = position === child.to ? child : split(node, child, position)
  }
  if (node.id < 0) {
    node.id = shapes.length
    shapes.push(keys)
  }
  return node.id
}
// Splits the edge into child at position; the returned middle node carries the prefix.
function split(parent: ShapeNode, child: ShapeNode, position: number): ShapeNode {
  const middle: ShapeNode = {
    from: child.from,
    id: -1,
    keys: child.keys,
    next: new Map<string, ShapeNode>().set(child.keys[position], child),
    to: position,
  }
  parent.next!.set(child.keys[child.from], middle)
  child.from = position
  return middle
}
