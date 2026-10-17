import type { Row, Frame, EncodeContext } from './contracts'
import { advances, closeFrame } from './frames'
import { leafCaptures } from './leaf'
import { recognize } from './facets/index'
import { encodeFail as fail } from './common'
import { internShape, shapeTrie } from './shapes'
// DFS.lean recursive_refines_stack / entries_unique, Inline.lean inline_matches_recursive and
// ShapeRadix.lean radix_matches_signature checked before implementation.
export function encodeGraph(value: unknown): string {
  const ids = new Map<object, number>()
  const nodes: Array<Row | undefined> = []
  const stack: Frame[] = []
  const shapes: string[][] = []
  const shapeRoot = shapeTrie()
  const owners = new Map<number, number>()
  const context: EncodeContext = {
    hasBuffers: false,
    ids,
    stack,
    token,
    owner(parameters, owner) {
      owners.set(parameters, owner)
    },
    shape(keys) {
      return internShape(shapeRoot, shapes, keys)
    },
  }
  function token(item: unknown): unknown {
    if (item === null) return null
    switch (typeof item) {
      case 'bigint': {
        const text = String(item)
        return [-6, text]
      }
      case 'boolean':
      case 'string':
        return item
      case 'number':
        return numberToken(item)
      case 'object':
        return objectToken(item)
      case 'undefined':
        return -1
      default:
        fail('unsupported value')
    }
  }
  function objectToken(item: object): number {
    let id = ids.get(item)
    if (id === undefined) {
      id = nodes.length
      ids.set(item, id)
      nodes.push(undefined)
      const kind = recognize(item)
      const captureLeaf = leafCaptures[kind.tag]
      if (captureLeaf !== undefined) nodes[id] = captureLeaf(item, context, kind.detail)
      else
        // Every frame starts with one field layout so the traversal stays monomorphic.
        stack.push({
          active: false,
          child: undefined,
          dense: false,
          detail: kind.detail,
          id,
          index: 0,
          input: undefined,
          iterator: undefined,
          keys: undefined,
          length: 0,
          mapValue: undefined,
          next: undefined,
          phase: 0,
          row: undefined,
          state: undefined,
          tag: kind.tag,
          value: item,
        } as unknown as Frame)
    }
    return -(id + 6)
  }
  let root
  try {
    root = token(value)
    // Each advance tokenizes children in place and yields only after a child pushed its own
    // frame, so that subtree completes before the parent's next observation.
    while (stack.length !== 0) {
      const frame = stack[stack.length - 1]
      if (advances[frame.tag](frame, context)) {
        nodes[frame.id] = frame.row
        stack.pop()
      }
    }
  } catch (error) {
    // Native IteratorClose on an abrupt throw preserves the original completion.
    for (let index = stack.length - 1; index >= 0; index--) {
      try {
        closeFrame(stack[index])
      } catch {}
    }
    throw error
  }
  for (const [parameters, owner] of owners) nodes[parameters] = [10, owner]
  return documentText(root, shapes, nodes, context.hasBuffers)
}
function documentText(
  root: unknown,
  shapes: string[][],
  nodes: Array<Row | undefined>,
  hasBuffers: boolean,
): string {
  let text
  if (hasBuffers) {
    const parts = new Array(nodes.length)
    for (let index = 0; index < nodes.length; index++) {
      const row = nodes[index]!
      parts[index] = row[0] === 7 ? '[7,"' + (row[1] as string) + '"]' : JSON.stringify(row)
    }
    text = '[' + JSON.stringify(root) + ',' + JSON.stringify(shapes) + ',[' + parts.join(',') + ']]'
  } else text = JSON.stringify([root, shapes, nodes])
  return text
}

function numberToken(item: number): number | number[] {
  if (!Number.isFinite(item)) return Number.isNaN(item) ? -2 : item > 0 ? -3 : -4
  if (Object.is(item, -0)) return -5
  return item < 0 ? [-7, item] : item
}
