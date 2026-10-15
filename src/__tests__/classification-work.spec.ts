// This specification inspects source-private state; keep imports on source modules in the package suite.
import { afterEach, describe, expect, it, vi } from 'vitest'
import { produce, reconcile, snapshot } from '../index.ts'
import * as kinds from '../adapters/recognition'

afterEach(() => vi.restoreAllMocks())

describe('classification work on repeated aliases', () => {
  it.each(['snapshot', 'unchanged', 'changed', 'reconcile'] as const)(
    'keeps %s recognition bounded by identities rather than occurrence count',
    (operation) => {
      const recognition = vi.spyOn(kinds, 'recognize')
      const validation = vi.spyOn(kinds, 'matchesKind')
      const checks: number[] = []
      const calls: number[] = []
      for (const width of [10, 1000]) {
        const shared = { value: 0 }
        const source = { items: Array.from({ length: width }, () => shared) }
        recognition.mockClear()
        validation.mockClear()
        if (operation === 'snapshot') snapshot(source)
        else if (operation === 'unchanged') produce(source, (draft) => draft)
        else if (operation === 'changed')
          produce(source, (draft) => {
            draft.items[0].value = 1
            return draft
          })
        else {
          const desired = { value: 1 }
          reconcile(source, { items: Array.from({ length: width }, () => desired) })
        }
        calls.push(recognition.mock.calls.length)
        checks.push(validation.mock.calls.length)
        expect(new Set(recognition.mock.calls.map(([, value]) => value)).size).toBe(
          operation === 'reconcile' ? 6 : 3,
        )
      }
      expect(calls[1]).toBe(calls[0])
      expect(checks[1]).toBe(checks[0])
      expect(checks[0]).toBe(operation === 'reconcile' ? 6 : 0)
      // Desired capture and current discovery classify unknown identities once.
      // Compiler/readback retain separate live expected-kind validation.
      expect(calls[0]).toBeLessThanOrEqual(operation === 'reconcile' ? 6 : 3)
    },
  )
})

it('also bounds recognition when a repeated current identity has an incompatible desired kind', () => {
  const recognition = vi.spyOn(kinds, 'recognize')
  const calls: number[] = []
  for (const width of [10, 1000]) {
    const current = new Date(0)
    const desired = { value: 1 }
    recognition.mockClear()
    const source = { items: Array.from({ length: width }, () => current) }
    reconcile(source, { items: Array.from({ length: width }, () => desired) })
    expect(source.items[0]).toEqual(desired)
    expect(source.items.every((item) => item === source.items[0])).toBe(true)
    calls.push(recognition.mock.calls.length)
  }
  expect(calls[0]).toBeGreaterThan(0)
  expect(calls[1]).toBe(calls[0])
})
it('ends cached kind certificates when an accessor read invalidates the observation lifetime', () => {
  const recognition = vi.spyOn(kinds, 'recognize')
  const leaf = { n: 0 }
  const source = {
    leaf,
    other: { m: 0 },
    get late(): number {
      return 1
    },
  }
  recognition.mockClear()
  produce(source, (draft) => {
    draft.other.m = 1
    return draft
  })
  // The accessor observation ends the certificate established before it, so the same
  // identity is recognized again afterwards instead of being served from the memo.
  const leafRecognitions = recognition.mock.calls.filter(([, value]) => value === leaf).length
  expect(leafRecognitions).toBeGreaterThanOrEqual(2)
})
