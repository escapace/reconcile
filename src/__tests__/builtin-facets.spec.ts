// Registry inspection uses source-private state; the public Set case also exercises the package.
import { expect, it } from 'vitest'
import { produce } from '../produce'
import { produce as produceSource } from '../produce.ts'
import { recognitionOrder } from '../../scripts/recognition-scan'
import { draftState } from '../types/shared/draft-collection'
import { snapshotTypes, publicationTypes, produceTypes } from '../types/builtins'
import { TEMPORAL_KIND } from '../types/temporal'
import { URL_KIND } from '../types/url'
import { URL_SEARCH_PARAMS_KIND } from '../types/url-search-parameters'

// The snapshot walk copies every other kind inline, so its registry lists only these.
const SNAPSHOT_FACETS: readonly symbol[] = [TEMPORAL_KIND, URL_KIND, URL_SEARCH_PARAMS_KIND]

it('uses global identities for the built-in kinds', () => {
  for (const symbol of recognitionOrder) {
    const key = Symbol.keyFor(symbol)
    expect(key).toMatch(/^@escapace\/reconcile\//)
    expect(Symbol.for(key!)).toBe(symbol)
  }
})

/** Each facet two registries both hold for `kind`, from the first and from the second. */
function sharedFacets(kind: symbol, first: object, second: object): Array<[unknown, unknown]> {
  const left = Reflect.get(first, kind) as object
  const right = Reflect.get(second, kind) as object
  return Reflect.ownKeys(left)
    .filter((key) => Reflect.has(right, key))
    .map((key) => [Reflect.get(left, key), Reflect.get(right, key)])
}

it('projects the same native callbacks into each public registry', () => {
  for (const kind of recognitionOrder) {
    const pairs = sharedFacets(kind, publicationTypes.policies, produceTypes.policies)
    if (SNAPSHOT_FACETS.includes(kind))
      pairs.push(...sharedFacets(kind, snapshotTypes.policies, publicationTypes.policies))
    for (const [left, right] of pairs) expect(left).toBe(right)
    expect(produceTypes.drafts[kind]).toBeDefined()
  }
})

it('lists in the snapshot registry only the kinds snapshot observes through their facets', () => {
  expect(new Set(Reflect.ownKeys(snapshotTypes.policies))).toEqual(new Set(SNAPSHOT_FACETS))
})

it('accepts global symbols as ordinary Set members without sentinel collisions', () => {
  const key = Symbol.for('@escapace/reconcile/lookup-not-found')
  const base = new Set([key, undefined])
  const next = produce(base, (draft) => {
    expect(draft.has(key)).toBe(true)
    expect(draft.has(undefined)).toBe(true)
    expect(draft.delete(key)).toBe(true)
    expect(draft.has(key)).toBe(false)
    return draft
  })
  expect(next).toEqual(new Set([undefined]))
  expect(base).toEqual(new Set([key, undefined]))
})

it('keeps registry configuration exposed through a collection draft frozen', () => {
  produceSource(new Map(), (draft) => {
    const state = draftState(draft) as unknown as {
      context: { types: typeof produceTypes }
    }
    expect(state.context.types).toBe(produceTypes)
    for (const kind of recognitionOrder) {
      const policy = state.context.types.policies[kind]
      const strategy = state.context.types.drafts[kind]
      expect(Object.isFrozen(policy)).toBe(true)
      expect(Object.isFrozen(policy.immutable)).toBe(true)
      expect(Object.isFrozen(strategy)).toBe(true)
      expect(Reflect.set(policy, 'someChild', policy.someChild)).toBe(false)
    }
    for (const operations of Object.getOwnPropertySymbols(produceTypes.specials).map(
      (kind) => produceTypes.specials[kind],
    ))
      expect(Object.isFrozen(operations)).toBe(true)
    return draft
  })
})
