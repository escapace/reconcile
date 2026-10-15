import { expect, it } from 'vitest'
import { createEngine } from '../engine'
import { defineType } from '../types/registry'
import { Cell, cellType } from './fixtures/cell-type'

for (const distinct of [false, true]) {
  it(`preserves custom construction responses through memo hits (distinct: ${distinct})`, () => {
    const root = new Cell(undefined)
    const child = new Cell(undefined)
    const target = new Cell(undefined)
    const response = distinct ? {} : target
    const responses = new Map<object, object>()
    const observed: unknown[] = []
    let constructionCalls = 0
    const custom = defineType({
      ...cellType,
      policy: {
        ...cellType.policy,
        construction(layout) {
          constructionCalls += 1
          return responses.get(layout)
        },
        observe(source, begin, edge) {
          const layout = { kind: cellType.kind } as const
          if (source === child) responses.set(layout, response)
          begin(layout)
          if (source === root) {
            observed.push(edge(child, 'first', cellType.kind, true))
            observed.push(edge(child, 'second', cellType.kind, true))
          }
        },
        snapshot(layout, _resolve, writer) {
          writer.initialize(
            layout,
            responses.has(layout) ? target : new Cell(undefined),
            () => undefined,
          )
        },
      },
    })
    createEngine({ types: [custom] }).snapshot(root)
    expect(observed).toEqual([response, response])
    expect(observed[0]).toBe(response)
    expect(observed[1]).toBe(response)
    expect(constructionCalls).toBe(3)
  })
}

it('clears prior metadata when a custom shared target later supplies its own identity', () => {
  const root = new Cell(undefined)
  const first = new Cell(undefined)
  const second = new Cell(undefined)
  const target = new Cell(undefined)
  const marker = {}
  const responses = new Map<object, object>()
  const observed: unknown[] = []
  const custom = defineType({
    ...cellType,
    policy: {
      ...cellType.policy,
      construction: (layout) => responses.get(layout),
      observe(source, begin, edge) {
        const layout = { kind: cellType.kind } as const
        if (source !== root) responses.set(layout, source === first ? marker : target)
        begin(layout)
        if (source === root) {
          observed.push(edge(first, 'first', cellType.kind, true))
          observed.push(edge(second, 'second', cellType.kind, true))
          observed.push(edge(first, 'again', cellType.kind, true))
        }
      },
      snapshot(layout, _resolve, writer) {
        writer.initialize(
          layout,
          responses.has(layout) ? target : new Cell(undefined),
          () => undefined,
        )
      },
    },
  })
  createEngine({ types: [custom] }).snapshot(root)
  expect(observed[0]).toBe(marker)
  expect(observed[1]).toBe(target)
  expect(observed[2]).toBe(target)
})

it('keeps a custom snapshot memo independent of later initializer writes', () => {
  const root = new Cell(undefined)
  const child = new Cell(undefined)
  const firstTarget = new Cell(undefined)
  const laterTarget = new Cell(undefined)
  const childLayouts = new Set<object>()
  const observed: unknown[] = []
  let reinitialize = () => undefined
  const custom = defineType({
    ...cellType,
    policy: {
      ...cellType.policy,
      construction: () => undefined,
      observe(source, begin, edge) {
        const layout = { kind: cellType.kind } as const
        if (source === child) childLayouts.add(layout)
        begin(layout)
        if (source === root) {
          edge(child, 'first')
          reinitialize()
          observed.push(edge(child, 'second', cellType.kind, true))
        }
      },
      snapshot(layout, _resolve, writer) {
        writer.initialize(layout, firstTarget, () => undefined)
        if (childLayouts.has(layout))
          reinitialize = () => {
            writer.initialize(layout, laterTarget, () => undefined)
            return undefined
          }
      },
    },
  })
  createEngine({ types: [custom] }).snapshot(root)
  expect(observed[0]).toBe(firstTarget)
})

it('looks up private references after a supplied memo getter reenters traversal', () => {
  const root = new Cell(undefined)
  const child = new Cell(undefined)
  let childObservations = 0
  let reenter = () => undefined
  let entered = false
  class ReentrantMemo extends WeakMap<object, object> {
    override get(source: object): object | undefined {
      if (source === child && !entered) {
        entered = true
        reenter()
        return undefined
      }
      return super.get(source)
    }
  }
  const custom = defineType({
    ...cellType,
    policy: {
      ...cellType.policy,
      observe(source, begin, edge) {
        begin({ kind: cellType.kind })
        if (source === child) childObservations += 1
        if (source === root) {
          reenter = () => {
            edge(child, 'inner')
            return undefined
          }
          edge(child, 'outer')
        }
      },
    },
  })
  createEngine({ types: [custom] }).snapshot(root, new ReentrantMemo())
  expect(childObservations).toBe(1)
})
