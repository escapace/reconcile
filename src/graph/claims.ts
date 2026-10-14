import { CLAIM_BIT_COUNT } from '../constants'
import type { Claims } from '../types'

const flag = (mode: number): number =>
  Number.isInteger(mode) && mode >= 0 && mode < CLAIM_BIT_COUNT ? 1 << mode : 0

export function claim(mode: number): Claims {
  const bit = flag(mode)
  return bit !== 0 ? bit : new Set([mode])
}

export function hasClaim(claims: Claims, mode: number): boolean {
  return typeof claims === 'number' ? (claims & flag(mode)) !== 0 : claims.has(mode)
}

/** Persistent insertion keeps earlier execution states' claim histories intact. */
export function withClaim(claims: Claims, mode: number): Claims {
  if (typeof claims === 'number') {
    const bit = flag(mode)
    if (bit !== 0) return claims | bit
  }
  return new Set(claimModes(claims)).add(mode)
}

/** Decodes the private representation for finite bridges and Set fallback. */
export function claimModes(claims: Claims): number[] {
  if (typeof claims !== 'number') return [...claims]
  const modes: number[] = []
  for (let mode = 0; mode < CLAIM_BIT_COUNT; mode += 1)
    if ((claims & (1 << mode)) !== 0) modes.push(mode)
  return modes
}
