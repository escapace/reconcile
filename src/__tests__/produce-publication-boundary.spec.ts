// This specification inspects source-private state; keep imports on source modules in the package suite.
import { describe, expect, it, vi } from 'vitest'
import { Finalization } from '../finalization'
import { produce } from '../produce.ts'
import { reconcile } from '../reconcile.ts'

vi.mock('../reconcile.ts', async () => {
  const actual = await vi.importActual<typeof import('../reconcile.ts')>('../reconcile.ts')
  return { ...actual, reconcile: vi.fn(actual.reconcile) }
})

describe('produce and caller publication boundary', () => {
  it('returns a finalized next graph without calling reconcile', () => {
    const reconcileSpy = vi.mocked(reconcile)
    reconcileSpy.mockClear()
    const current = { nested: { count: 0 }, untouched: { keep: true } }
    const result = produce(current, (draft) => {
      draft.nested.count = 1
      return draft
    })
    expect(reconcileSpy).not.toHaveBeenCalled()
    expect(result).toEqual({ nested: { count: 1 }, untouched: { keep: true } })
    expect(result).not.toBe(current)
    expect(result.untouched).toBe(current.untouched)
    expect(current.nested.count).toBe(0)
  })

  it('executes one recipe before publishing once onto the same current root', () => {
    const reconcileSpy = vi.mocked(reconcile)
    reconcileSpy.mockClear()
    const current = { nested: { count: 0 } }
    const recipe = vi.fn((draft: typeof current) => {
      draft.nested.count = 1
      return draft
    })
    const next = produce(current, recipe)
    expect(recipe).toHaveBeenCalledTimes(1)
    expect(reconcileSpy).not.toHaveBeenCalled()
    expect(current.nested.count).toBe(0)
    const result = reconcile(current, next)
    expect(reconcileSpy).toHaveBeenCalledTimes(1)
    expect(reconcileSpy.mock.calls[0]?.[0]).toBe(current)
    expect(reconcileSpy.mock.calls[0]?.[1]).toBe(next)
    expect(result).toBe(current)
    expect(result.nested.count).toBe(1)
  })

  it('does not publish when the recipe throws', () => {
    const reconcileSpy = vi.mocked(reconcile)
    reconcileSpy.mockClear()
    const current = { count: 0 }
    const failure = new Error('recipe failed')
    const recipe = vi.fn((draft: typeof current) => {
      draft.count = 1
      throw failure
    })
    expect(() => reconcile(current, produce(current, recipe))).toThrow(failure)
    expect(recipe).toHaveBeenCalledTimes(1)
    expect(reconcileSpy).not.toHaveBeenCalled()
    expect(current.count).toBe(0)
  })

  it('does not publish when finalization throws', () => {
    const reconcileSpy = vi.mocked(reconcile)
    reconcileSpy.mockClear()
    const current = { count: 0 }
    const failure = new Error('finalization failed')
    const finalizationSpy = vi.spyOn(Finalization.prototype, 'run').mockImplementationOnce(() => {
      throw failure
    })
    try {
      expect(() =>
        reconcile(
          current,
          produce(current, (draft) => {
            draft.count = 1
            return draft
          }),
        ),
      ).toThrow(failure)
      expect(finalizationSpy).toHaveBeenCalledTimes(1)
      expect(reconcileSpy).not.toHaveBeenCalled()
      expect(current.count).toBe(0)
    } finally {
      finalizationSpy.mockRestore()
    }
  })
})
