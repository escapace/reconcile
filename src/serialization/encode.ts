import type { Row, Frame, EncodeContext } from './contracts'
import { advances, closeFrame } from './frames'
import { leafCaptures } from './leaf'
import { recognize } from './facets/index'
import { encodeFail as fail } from './common'
// DFS.lean recursive_refines_stack and entries_unique checked before implementation.
export function encodeGraph(value: unknown): string {
  const ids = new Map<object, number>()
  const nodes: Array<Row | undefined> = []
  const stack: Frame[] = []
  const shapes: string[][] = []
  const shapeIds = new Map<string, number>()
  const owners = new Map<number, number>()
  const context: EncodeContext = {
    hasBuffers: false,
    ids,
    owner(parameters, owner) {
      owners.set(parameters, owner)
    },
    shape(keys) {
      const signature = JSON.stringify(keys)
      let id = shapeIds.get(signature)
      if (id === undefined) {
        id = shapes.length
        shapeIds.set(signature, id)
        shapes.push(keys)
      }
      return id
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
        return [-1]
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
        // eslint-disable-next-line typescript/consistent-type-assertions -- Continuation fields are initialized by their phase before use.
        stack.push({
          detail: kind.detail,
          id,
          input: undefined,
          phase: 0,
          tag: kind.tag,
          value: item,
        } as Frame)
    }
    return -(id + 1)
  }
  let root
  try {
    root = token(value)
    while (stack.length !== 0) {
      const frame = stack[stack.length - 1]
      if (advances[frame.tag](frame, context)) {
        nodes[frame.id] = frame.row
        stack.pop()
      } else frame.input = token(frame.child)
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
  if (!Number.isFinite(item)) return [Number.isNaN(item) ? -2 : item > 0 ? -3 : -4]
  if (Object.is(item, -0)) return [-5]
  return item < 0 ? [-7, item] : item
}
