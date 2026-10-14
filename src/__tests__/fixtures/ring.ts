export interface RingNode {
  payload: { value: number }
  next?: RingNode
}

export function ring(length: number): RingNode[] {
  const nodes: RingNode[] = Array.from({ length }, () => ({ payload: { value: 0 } }))
  nodes.forEach((node, index) => {
    node.next = nodes[(index + 1) % length]
  })
  return nodes
}
