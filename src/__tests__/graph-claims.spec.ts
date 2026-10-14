import { expect, it } from 'vitest'
import { claim, claimModes, hasClaim, withClaim } from '../graph/claims'
import type { Claims } from '../types'

it('agrees with finite Set membership and insertion for every nine-mode subset', () => {
  for (let mask = 0; mask < 512; mask += 1) {
    const modes = Array.from({ length: 9 }, (_, mode) => mode)
    const expected = new Set(modes.filter((mode) => (mask & (1 << mode)) !== 0))
    expect(new Set(claimModes(mask))).toEqual(expected)
    for (const mode of modes) {
      expect(hasClaim(mask, mode)).toBe(expected.has(mode))
      const next = withClaim(mask, mode)
      expect(typeof next).toBe('number')
      expect(new Set(claimModes(next))).toEqual(new Set([...expected, mode]))
      expect(new Set(claimModes(mask))).toEqual(expected)
    }
  }
})

it('uses all safe bits without aliases at the signed/shift boundary', () => {
  let claims: Claims = 0
  for (let mode = 0; mode < 31; mode += 1) {
    expect(hasClaim(claims, mode)).toBe(false)
    claims = withClaim(claims, mode)
  }
  expect(claims).toBe(2 ** 31 - 1)
  for (let mode = 0; mode < 31; mode += 1) expect(hasClaim(claims, mode)).toBe(true)
  for (const mode of [31, 32, 62, 2 ** 32, -1, Number.NaN, Infinity, 0.5])
    expect(hasClaim(claims, mode)).toBe(false)
})

it('preserves arbitrary numeric labels through persistent fallback without truncation', () => {
  const modes = [30, 31, 32, 62, 2 ** 32, -1, Number.NaN, Infinity, 0.5, -0]
  for (const initial of modes) {
    let claims = claim(initial)
    const expected = new Set([initial])
    for (const mode of modes) {
      const previous = claims
      const before = new Set(expected)
      claims = withClaim(claims, mode)
      expected.add(mode)
      expect(new Set(claimModes(previous))).toEqual(before)
      expect(new Set(claimModes(claims))).toEqual(expected)
      for (const query of modes) expect(hasClaim(claims, query)).toBe(expected.has(query))
    }
  }
})
