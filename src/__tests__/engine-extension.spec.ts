import { OBJECT_KIND } from '../types/object'
import { describe, expect, it } from 'vitest'
import { createEngine } from '../engine'
import { ReconcileError } from '../error'
import { builtinModules } from '../types/builtins'
import { Cell, cellType } from './fixtures/cell-type'

const engine = createEngine({ types: [cellType, ...builtinModules] })

describe('instance-scoped native type extension', () => {
  it('registers a new kind without changing another engine or the built-in fallback', () => {
    const ordinary = createEngine()
    const cell = new Cell(1)
    expect(engine.types.recognize(cell)).toBe(cellType.kind)
    expect(ordinary.types.recognize(cell)).toBe(OBJECT_KIND)
    expect(Object.isFrozen(engine)).toBe(true)
  })

  it('captures, constructs and snapshots mixed cycles through the registered policy', () => {
    const cell = new Cell(undefined)
    const source = { again: cell, cell, map: new Map([['cell', cell]]) }
    cell.value = source
    const result = engine.snapshot(source) as typeof source
    expect(result).not.toBe(source)
    expect(result.cell).toBeInstanceOf(Cell)
    expect(result.cell).not.toBe(cell)
    expect(result.again).toBe(result.cell)
    expect(result.cell.value).toBe(result)
    expect(result.map.get('cell')).toBe(result.cell)
  })

  it('drafts nested values, preserves the input and restores undo identities', () => {
    const child = { n: 0 }
    const source = new Cell(child)
    const result = engine.produce(source, (draft) => {
      ;(draft.value as typeof child).n = 2
      return draft
    })
    expect(result).toBeInstanceOf(Cell)
    expect(result).not.toBe(source)
    expect(result.value).toEqual({ n: 2 })
    expect(source.value).toBe(child)
    expect(child.n).toBe(0)
    expect(
      engine.produce(source, (draft) => {
        draft.value = 1
        draft.value = child
        return draft
      }),
    ).toBe(source)
  })

  it('publishes into a retained Cell root and respects fixed child requirements', () => {
    const child = { n: 0 }
    const current = Object.freeze(new Cell(child))
    expect(engine.reconcile(current, new Cell({ n: 3 }))).toBe(current)
    expect(current.value).toBe(child)
    expect(child.n).toBe(3)
    expect(() => engine.reconcile(Object.freeze(new Cell(1)), new Cell(2))).toThrow(ReconcileError)
  })

  it('composes production through the same configured draft and publication paths', () => {
    const source = new Cell(1)
    expect(
      engine.reconcile(
        source,
        engine.produce(source, (draft) => {
          draft.value = 2
          return draft
        }),
      ),
    ).toBe(source)
    expect(source.value).toBe(2)
  })
})
