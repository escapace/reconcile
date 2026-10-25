import { hasOwn } from '../../object-property'
import type { Align, CapturedNode, SlotRead } from '../../types'
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

/** The own value of `current` at `key`, or `undefined` when it has none. */
export const ownValue: SlotRead = (current, key) =>
  hasOwn(current, key) ? Reflect.get(current, key) : undefined

/** Visits the slot of each key of `node` on `current`, reading each own value once. */
export function alignedProperties(
  node: CapturedNode,
  current: object | undefined,
  visit: Align,
  read: SlotRead = ownValue,
): void {
  for (let index = 0; index < node.keys.length; index += 1)
    visit(
      current === undefined ? undefined : read(current, node.keys[index]),
      node.edges[index],
      index,
    )
}
