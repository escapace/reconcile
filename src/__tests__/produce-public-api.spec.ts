import { describe, expect, expectTypeOf, it } from 'vitest'
import * as API from '../index'

const { produce } = API

describe('public API', () => {
  it('exports graph and serialization operations and the error surface', () => {
    expect(Object.keys(API).sort()).toEqual([
      'RECONCILE_ERROR_TYPES',
      'ReconcileError',
      'deserialize',
      'isReconcileError',
      'isReconcileErrorOfType',
      'produce',
      'reconcile',
      'requiredMaxBytes',
      'serialize',
      'snapshot',
    ])
    expectTypeOf<keyof typeof API>().toEqualTypeOf<
      | 'deserialize'
      | 'isReconcileError'
      | 'isReconcileErrorOfType'
      | 'produce'
      | 'RECONCILE_ERROR_TYPES'
      | 'reconcile'
      | 'ReconcileError'
      | 'requiredMaxBytes'
      | 'serialize'
      | 'snapshot'
    >()
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
