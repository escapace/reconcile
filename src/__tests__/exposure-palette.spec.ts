import { describe, expect, it } from 'vitest'
import { reactive, readonly, shallowReactive, shallowReadonly } from 'vue'
import { storageIdentity } from '../adapters/vue'
import {
  BuiltinExposurePalette as ExposurePalette,
  builtinExposureMode as exposureMode,
} from './fixtures/builtin-exposure'

describe('finite Vue exposure certification', () => {
  it.each([{}, [], new Map(), new Set()])('classifies the wrapping closure for %s', (base) => {
    const palette = new ExposurePalette()
    const identities = new Set<object>([base])
    for (const value of identities)
      for (const wrap of [reactive, readonly, shallowReactive, shallowReadonly])
        identities.add(wrap(value))
    expect(identities.size).toBe(9)
    expect([...identities].map(exposureMode).sort((a, b) => a! - b!)).toEqual([
      0, 1, 2, 3, 4, 5, 6, 7, 8,
    ])
    expect([...identities].map((value) => palette.observe(value)?.storage)).toEqual(
      Array.from({ length: 9 }, () => base),
    )
    expect([...identities].every((value) => palette.observe(value) !== undefined)).toBe(true)
  })

  it('does not invent additional special-value exposure options', () => {
    for (const base of [
      new Date(),
      new ArrayBuffer(4),
      new Uint8Array(4),
      new DataView(new ArrayBuffer(4)),
    ])
      for (const wrap of [reactive, readonly, shallowReactive, shallowReadonly]) {
        expect(wrap(base)).toBe(base)
        expect(exposureMode(base)).toBe(0)
      }
  })

  it('rejects two different handles claiming the same mode and storage', () => {
    const raw = {}
    const wrapper = () => ({ __v_isReactive: true, __v_raw: raw })
    const first = wrapper()
    const second = wrapper()
    const palette = new ExposurePalette()
    expect(storageIdentity(first)).toBe(raw)
    expect(palette.observe(first)).toEqual({ mode: 1, storage: raw })
    expect(palette.observe(second)).toBeUndefined()
  })

  it('does not evaluate application accessor markers', () => {
    let reads = 0
    const value = {
      get __v_raw() {
        reads += 1
        return {}
      },
    }
    expect(exposureMode(value)).toBe(0)
    expect(reads).toBe(0)
  })
})
