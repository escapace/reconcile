// Registry inspection uses source-private state; the public Set case also exercises the package.
import { expect, it } from 'vitest'
import { produce } from '../produce'
import { produce as produceSource } from '../produce.ts'
import { MODULE_BRAND } from '../constants'
import { draftState } from '../types/shared/draft-collection'
import { builtinModules, snapshotTypes, publicationTypes, produceTypes } from '../types/builtins'

const SNAPSHOT_FACETS = ['temporal', 'url', 'url-search-params']

it('uses global identities for the built-in protocol symbols', () => {
  for (const symbol of [MODULE_BRAND, ...builtinModules.map((type) => type.kind)]) {
    const key = Symbol.keyFor(symbol)
    expect(key).toMatch(/^@escapace\/reconcile\//)
    expect(Symbol.for(key!)).toBe(symbol)
  }
})

it('projects the same native callbacks into each public registry', () => {
  for (const module of builtinModules) {
    const registries = SNAPSHOT_FACETS.includes(module.name)
      ? [snapshotTypes, publicationTypes, produceTypes]
      : [publicationTypes, produceTypes]
    for (const registry of registries) {
      const policy = registry.policies[module.kind]
      for (const key of Reflect.ownKeys(policy)) {
        const actual: unknown = Reflect.get(policy, key)
        const expected: unknown = Reflect.get(module.policy, key)
        // defineType freezes copies of metadata; the native callbacks must be identical.
        expect(actual).toEqual(expected)
      }
    }
    expect(produceTypes.drafts[module.kind]).toEqual(module.draft)
  }
})

// The snapshot walk copies every other kind inline, so its registry lists only these.
it('lists in the snapshot registry only the kinds snapshot observes through their facets', () => {
  const kinds = builtinModules
    .filter((module) => SNAPSHOT_FACETS.includes(module.name))
    .map((module) => module.kind)
  expect(new Set(Reflect.ownKeys(snapshotTypes.policies))).toEqual(new Set(kinds))
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
    for (const module of builtinModules) {
      const policy = state.context.types.policies[module.kind]
      const strategy = state.context.types.drafts[module.kind]
      expect(Object.isFrozen(policy)).toBe(true)
      expect(Object.isFrozen(policy.bindings)).toBe(true)
      expect(Object.isFrozen(policy.immutable)).toBe(true)
      expect(Object.isFrozen(strategy)).toBe(true)
      expect(Reflect.set(policy, 'allocate', policy.allocate)).toBe(false)
    }
    for (const operations of Object.getOwnPropertySymbols(produceTypes.specials).map(
      (kind) => produceTypes.specials[kind],
    ))
      expect(Object.isFrozen(operations)).toBe(true)
    return draft
  })
})
