import { createEngine } from '../engine'
import { builtinModules } from '../types/builtins'
import { defineType } from '../types/registry'
import { Cell, cellType } from './fixtures/cell-type'
import { expect, it } from 'vitest'
import { constructionOrder } from '../graph/construction'

it('allocates shells before views in captured order, including retained backing stores', () => {
  expect(constructionOrder([[3], [], [1], []], [false, true, false, false])).toEqual([3, 0, 2])
})

it('supports several dependency layers and shared construction prerequisites', () => {
  expect(constructionOrder([[2, 3], [0], [3], []], [false, false, false, false])).toEqual([
    3, 2, 0, 1,
  ])
})

it('rejects fresh construction cycles while allowing cycles broken by retained identities', () => {
  expect(constructionOrder([[1], [0]], [false, false])).toBeUndefined()
  expect(constructionOrder([[1], [0]], [true, false])).toEqual([1])
  expect(constructionOrder([[0]], [true])).toEqual([])
  expect(constructionOrder([[0]], [false])).toBeUndefined()
})

it('counts duplicate dependencies while keeping allocation order independent of queue admission', () => {
  expect(constructionOrder([[3, 3], [2], [], []], [false, false, false, false])).toEqual([
    2, 3, 0, 1,
  ])
  expect(constructionOrder([[], [0, 0], []], [true, false, false])).toEqual([2, 1])
  expect(constructionOrder([[1, 1], [0]], [false, false])).toBeUndefined()
})

it('constructs a registered three-layer native chain through the unchanged core', () => {
  const events: unknown[] = []
  const linked = defineType({
    ...cellType,
    policy: {
      ...cellType.policy,

      bindings: {
        tag: 'dependent' as const,
        dependencies: (node) =>
          node.edges.flatMap((edge) => (edge.node !== undefined ? [edge.node] : [])),
        read: (node, target) =>
          node.edges.flatMap((edge) =>
            edge.node !== undefined
              ? [{ identity: (target as Cell).value as object, node: edge.node }]
              : [],
          ),
      },
      allocate: (node, resolve) => {
        const value = resolve(node.edges[0])
        events.push(value)
        return new Cell(value)
      },
    },
    requires: [cellType.kind],
  })
  const engine = createEngine({ types: [linked, ...builtinModules] })
  const current: { cell?: Cell } = {}
  const desired = new Cell(new Cell(new Cell(1)))
  const result = engine.reconcile(current, { cell: desired })
  expect(result).toBe(current)
  expect(result.cell).toEqual(desired)
  expect(result.cell).not.toBe(desired)
  expect(events).toEqual([1, (result.cell.value as Cell).value, result.cell.value])
  events.length = 0
  const patched = engine.produce(result, (draft) => {
    ;((draft.cell.value as Cell).value as Cell).value = 2
    return draft
  })
  expect(((result.cell.value as Cell).value as Cell).value).toBe(1)
  expect(((patched.cell.value as Cell).value as Cell).value).toBe(2)
  expect(events).toEqual([2, (patched.cell.value as Cell).value, patched.cell.value])
})
