// Compares production carrier adoption with the finite query/identity projection.
// Admission, construction metadata and forced reuse are covered by native graph tests.
import assert from 'node:assert/strict'
import { readFileSync } from 'node:fs'
import { adoptURLCarrier, createURLCarrier } from '../src/types/shared/url-carrier'
import type { Oracle } from './lean-oracle'

interface Fixture {
  href: string
  text: string
  touched: boolean
}
interface Observation {
  child: number
  entries: Array<[string, string]>
  owner: number
  query: string
}

function query(url: URL): string {
  const withoutFragment = url.href.split('#', 1)[0]
  const position = withoutFragment.indexOf('?')
  return position === -1 ? '' : withoutFragment.slice(position)
}

/** Uses native parsing as an explicit label supplier, not as a Lean-proved operation. */
export async function checkOwnedNativeChildRuntime(oracle: Oracle): Promise<void> {
  const fixtures = JSON.parse(
    readFileSync('lean/owned-native-child-fixtures.json', 'utf8'),
  ) as Fixture[]
  const inputs = []
  const actual: Observation[] = []
  for (const fixture of fixtures) {
    const carrier = createURLCarrier(fixture.text)
    const child = carrier.searchParams
    const captured = [...child]
    if (fixture.touched) URLSearchParams.prototype.delete.call(child, '__absent_from_fixture__')
    const source = new URL(fixture.href)
    const text = child.toString()
    inputs.push({
      actualChild: 1,
      canonicalQuery: text === '' ? '' : `?${text}`,
      captured,
      child: 1,
      equal: true,
      forced: false,
      metadata: null,
      owner: 0,
      ownerChanged: false,
      source: [...source.searchParams],
      sourceQuery: query(source),
      touched: fixture.touched,
    })
    const adopted = adoptURLCarrier(carrier, fixture.href)
    // Labels are conditional on actual native identity checks, never assigned by value.
    assert.equal(adopted, carrier)
    assert.equal(adopted.searchParams, child)
    actual.push({ child: 1, entries: [...adopted.searchParams], owner: 0, query: query(adopted) })
  }
  const expected = JSON.parse(
    await oracle('OwnedNativeChild', [], { input: JSON.stringify(inputs) }),
  ) as Observation[]
  assert.deepEqual(
    actual,
    expected.map(({ child, entries, owner, query: rawQuery }) => ({
      child,
      entries,
      owner,
      query: rawQuery,
    })),
  )
  console.log(`OwnedNativeChild: ${actual.length} production carrier adoption projections`)
}
