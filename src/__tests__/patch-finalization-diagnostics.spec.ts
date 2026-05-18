import { describe, expect, it, vi } from 'vitest'

vi.mock('../reconcile', async () => {
  const actual = await vi.importActual<typeof import('../reconcile')>('../reconcile')

  return {
    ...actual,
    reconcile: vi.fn(actual.reconcile),
  }
})

describe('patch finalization diagnostics', () => {
  it('keeps an unread sibling on the original reference when only an accessed child changes', async () => {
    const patchModule = await import('../patch')
    const left = { count: 0 }
    const right = { keep: true }
    const current = {
      left,
      right,
    }

    const result = patchModule.createPatch(current, (draft) => {
      draft.left.count = 1
      return draft
    })

    expect(result.left).not.toBe(left)
    expect(result.right).toBe(right)
    expect(current.left.count).toBe(0)
  })

  it('stays on the original result for same-value child writes and diverges only on the first real child mutation', async () => {
    const patchModule = await import('../patch')
    const current = {
      child: { count: 0 },
    }

    const sameValueResult = patchModule.createPatch(current, (draft) => {
      draft.child.count = 0
      return draft
    })

    const changedResult = patchModule.createPatch(current, (draft) => {
      draft.child.count = 1
      return draft
    })

    expect(sameValueResult).toBe(current)
    expect(changedResult).not.toBe(current)
    expect(changedResult.child).not.toBe(current.child)
    expect(changedResult.child.count).toBe(1)
    expect(current.child.count).toBe(0)
  })

  it('reuses the original result on no-op finalization', async () => {
    const patchModule = await import('../patch')
    const current = {
      nested: { count: 0 },
    }

    const result = patchModule.createPatch(current, (draft) => {
      void draft.nested.count
      return draft
    })

    expect(result).toBe(current)
  })

  it('diverges from the original current value after a reverted nested mutation', async () => {
    // Under the monotonic write model, the first real mutation permanently marks the nested
    // draft modified. Writing the original value back is a second real mutation, not a
    // restoration, so the finalized next value is a fresh image rather than the original
    // current reference.
    const patchModule = await import('../patch')
    const current = {
      nested: { count: 0 },
    }

    const result = patchModule.createPatch(current, (draft) => {
      draft.nested.count = 1
      draft.nested.count = 0
      return draft
    })

    expect(result).not.toBe(current)
    expect(result.nested).not.toBe(current.nested)
    expect(result.nested.count).toBe(0)
    expect(current.nested.count).toBe(0)
  })

  it('treats set membership reads as no-op and diverges on the first mutating set operation', async () => {
    const patchModule = await import('../patch')
    const item = { id: 1 }
    const current = {
      item,
      set: new Set<object>([item]),
    }

    const readOnlyResult = patchModule.createPatch(current, (draft) => {
      expect(draft.set.has(draft.item)).toBe(true)
      return draft
    })

    const changedResult = patchModule.createPatch(current, (draft) => {
      expect(draft.set.has(draft.item)).toBe(true)
      draft.set.delete(draft.item)
      draft.set.add({ id: 2 })
      return draft
    })

    expect(readOnlyResult).toBe(current)
    expect(changedResult).not.toBe(current)
    expect(Array.from(changedResult.set.values())).toEqual([{ id: 2 }])
    expect(Array.from(current.set.values())).toEqual([item])
  })

  it('repairs repeated-reference finalization into one finalized image', async () => {
    const patchModule = await import('../patch')
    const current = {
      item: { count: 0 },
    }

    const result = patchModule.createPatch(current, (draft) => {
      draft.item.count = 2

      return {
        left: draft.item,
        right: draft.item,
      }
    })

    expect(result.left).toBe(result.right)
    expect(result).toEqual({
      left: { count: 2 },
      right: { count: 2 },
    })
  })

  it('repairs collection-captured finalization into one finalized image', async () => {
    const patchModule = await import('../patch')
    const current = {
      item: { count: 0 },
    }

    const result = patchModule.createPatch(current, (draft) => {
      draft.item.count = 3

      return {
        list: [draft.item],
        map: new Map<string, { count: number }>([['item', draft.item]]),
      }
    })

    expect(result.list[0]).toBe(result.map.get('item'))
    expect(result.list[0]).toEqual({ count: 3 })
  })

  it('keeps createPatch on the recipe-return boundary and does not publish through reconcile', async () => {
    const reconcileModule = await import('../reconcile')
    const patchModule = await import('../patch')
    const reconcileSpy = vi.mocked(reconcileModule.reconcile)

    reconcileSpy.mockClear()

    const result = patchModule.createPatch({ nested: { count: 0 } }, (draft) => {
      draft.nested.count = 4
      return draft.nested
    })

    expect(reconcileSpy).not.toHaveBeenCalled()
    expect(result).toEqual({ count: 4 })
  })

  it('preserves one coherent next-side buffer for an ordinary returned root that exposes the same buffer directly and through multiple child views', async () => {
    const patchModule = await import('../patch')
    const buffer = new Uint8Array([1, 2, 3, 4]).buffer
    const current = {
      typed: new Uint8Array(buffer),
      view: new DataView(buffer),
    }

    const result = patchModule.createPatch(current, (draft) => {
      draft.view.setUint8(1, 9)

      return {
        buffer: draft.view.buffer,
        left: new Uint8Array(draft.view.buffer, 0, 2),
        nested: {
          mirror: draft.view.buffer,
          right: new DataView(draft.view.buffer, 2, 2),
        },
      }
    }) as {
      buffer: ArrayBuffer
      left: Uint8Array
      nested: {
        mirror: ArrayBuffer
        right: DataView
      }
    }

    expect(result.buffer).toBe(result.left.buffer)
    expect(result.buffer).toBe(result.nested.mirror)
    expect(result.buffer).toBe(result.nested.right.buffer)
    expect(Array.from(new Uint8Array(result.buffer))).toEqual([1, 9, 3, 4])
    expect(Array.from(result.left)).toEqual([1, 9])
    expect(
      Array.from(
        new Uint8Array(
          result.nested.right.buffer,
          result.nested.right.byteOffset,
          result.nested.right.byteLength,
        ),
      ),
    ).toEqual([3, 4])
  })

  it('publishes one coherent next-side buffer for an ordinary returned root that exposes the same buffer directly and through multiple child views', async () => {
    const patchModule = await import('../patch')
    const buffer = new Uint8Array([1, 2, 3, 4]).buffer
    const current = {
      typed: new Uint8Array(buffer),
      view: new DataView(buffer),
    }

    const result = patchModule.patch(current, (draft) => {
      draft.view.setUint8(1, 9)

      return {
        buffer: draft.view.buffer,
        left: new Uint8Array(draft.view.buffer, 0, 2),
        nested: {
          mirror: draft.view.buffer,
          right: new DataView(draft.view.buffer, 2, 2),
        },
      }
    }) as {
      buffer: ArrayBuffer
      left: Uint8Array
      nested: {
        mirror: ArrayBuffer
        right: DataView
      }
    }

    expect(result.buffer).toBe(result.left.buffer)
    expect(result.buffer).toBe(result.nested.mirror)
    expect(result.buffer).toBe(result.nested.right.buffer)
    expect(Array.from(new Uint8Array(result.buffer))).toEqual([1, 9, 3, 4])
    expect(Array.from(result.left)).toEqual([1, 9])
    expect(
      Array.from(
        new Uint8Array(
          result.nested.right.buffer,
          result.nested.right.byteOffset,
          result.nested.right.byteLength,
        ),
      ),
    ).toEqual([3, 4])
  })
})
