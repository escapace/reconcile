import { expect, it } from 'vitest'
import { recognitionOrder } from '../../scripts/check/fixtures/recognition-scan'
import { snapshotTypes, publicationTypes, produceTypes } from '../types/builtins'
import { TEMPORAL_KIND } from '../types/temporal'
import { URL_KIND } from '../types/url'
import { URL_SEARCH_PARAMS_KIND } from '../types/url-search-parameters'

// The snapshot walk copies every other kind inline, so its registry lists only these.
const SNAPSHOT_FACETS: readonly symbol[] = [TEMPORAL_KIND, URL_KIND, URL_SEARCH_PARAMS_KIND]

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
    // A facet built per registry, as URL capture is with its own operation's error, shares the
    // code of its callbacks rather than their identity.
    for (const [left, right] of pairs)
      expect(left === right || String(left) === String(right)).toBe(true)
    expect(produceTypes.drafts[kind]).toBeDefined()
  }
})

it('lists in the snapshot registry only the kinds snapshot observes through their facets', () => {
  expect(new Set(Reflect.ownKeys(snapshotTypes.policies))).toEqual(new Set(SNAPSHOT_FACETS))
})
