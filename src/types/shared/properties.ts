import { isNode } from '../../graph/edge'
import { hasOwn } from '../../object-property'
import type { Align, CapturedNode } from '../../types'
import { isDataDescriptor } from '../../standard-prototypes'

export function backedProperty(
  base: object | undefined,
  key: PropertyKey,
  value: unknown,
): boolean {
  return (
    base !== undefined &&
    isDataDescriptor(Object.getOwnPropertyDescriptor(base, key) ?? {}) &&
    Object.is(value, Reflect.get(base, key))
  )
}

export function alignedProperties(
  node: CapturedNode,
  current: object | undefined,
  visit: Align,
): void {
  for (let index = 0; index < node.keys.length; index += 1) {
    const edge = node.edges[index]
    if (isNode(edge)) {
      const key = node.keys[index]
      visit(
        current !== undefined && hasOwn(current, key) ? Reflect.get(current, key) : undefined,
        edge,
        index,
      )
    }
  }
}
