import { describe, expect, it, vi } from 'vitest'

vi.mock('../reconcile', async () => {
  const actual = await vi.importActual<typeof import('../reconcile')>('../reconcile')

  return {
    ...actual,
    reconcile: vi.fn(actual.reconcile),
  }
})

describe('patch publication boundary', () => {
  it('createPatch returns a finalized next graph without calling reconcile', async () => {
    const reconcileModule = await import('../reconcile')
    const patchModule = await import('../patch')
    const reconcileSpy = vi.mocked(reconcileModule.reconcile)

    reconcileSpy.mockClear()

    const current = {
      nested: { count: 0 },
      untouched: { keep: true },
    }

    const result = patchModule.createPatch(current, (draft) => {
      draft.nested.count = 1
      return draft
    })

    expect(reconcileSpy).not.toHaveBeenCalled()
    expect(result).toEqual({
      nested: { count: 1 },
      untouched: { keep: true },
    })
    expect(result).not.toBe(current)
    expect(result.untouched).toBe(current.untouched)
    expect(current.nested.count).toBe(0)
  })

  it('patch calls reconcile exactly once for one recipe execution', async () => {
    const reconcileModule = await import('../reconcile')
    const patchModule = await import('../patch')
    const reconcileSpy = vi.mocked(reconcileModule.reconcile)

    reconcileSpy.mockClear()

    const current = {
      nested: { count: 0 },
    }

    const result = patchModule.patch(current, (draft) => {
      draft.nested.count = 1
      return draft
    })

    expect(reconcileSpy).toHaveBeenCalledTimes(1)
    expect(reconcileSpy.mock.calls[0]?.[0]).toBe(current)
    expect(reconcileSpy.mock.calls[0]?.[1]).toEqual({
      nested: { count: 1 },
    })
    expect(result).toBe(current)
    expect(result.nested.count).toBe(1)
  })
})
