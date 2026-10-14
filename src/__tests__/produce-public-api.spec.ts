import { describe, expect, expectTypeOf, it } from 'vitest'
import * as API from '../index'
import { createEngine } from '../engine'

const { produce } = API

describe('three-operation public API', () => {
  it('exports the three operations and the error surface', () => {
    expect(Object.keys(API).sort()).toEqual([
      'RECONCILE_ERROR_TYPES',
      'ReconcileError',
      'isReconcileError',
      'isReconcileErrorOfType',
      'produce',
      'reconcile',
      'snapshot',
    ])
    expectTypeOf<keyof typeof API>().toEqualTypeOf<
      | 'isReconcileError'
      | 'isReconcileErrorOfType'
      | 'produce'
      | 'RECONCILE_ERROR_TYPES'
      | 'reconcile'
      | 'ReconcileError'
      | 'snapshot'
    >()
  })

  it('exposes only the retained operations on a configured engine', () => {
    const engine = createEngine()
    expect(Object.keys(engine).sort()).toEqual(['produce', 'reconcile', 'snapshot', 'types'])
    expectTypeOf<keyof typeof engine>().toEqualTypeOf<
      'produce' | 'reconcile' | 'snapshot' | 'types'
    >()
    expect(Object.isFrozen(engine)).toBe(true)
  })

  it('infers draft, nested, replacement, primitive, and void return types', () => {
    const current = { nested: { count: 0 } }
    const root = produce(current, (draft) => draft)
    expectTypeOf(root).toEqualTypeOf<typeof current>()
    expect(root).toBe(current)

    const nested = produce(current, (draft) => {
      draft.nested.count = 1
      return draft.nested
    })
    expectTypeOf(nested).toEqualTypeOf<{ count: number }>()
    expect(nested).toEqual({ count: 1 })
    expect(current.nested.count).toBe(0)

    const replacement = produce(current, () => ({ replacement: true as const }))
    expectTypeOf(replacement).toEqualTypeOf<{ replacement: true }>()
    expect(replacement).toEqual({ replacement: true })

    const primitive = produce(current, () => 7)
    expectTypeOf(primitive).toEqualTypeOf<number>()
    expect(primitive).toBe(7)

    const noReturn = produce(current, (draft) => {
      draft.nested.count = 9
    })
    expectTypeOf(noReturn).toEqualTypeOf<ReturnType<() => void>>()
    expect(noReturn).toBeUndefined()
    expect(current.nested.count).toBe(0)
  })
})
