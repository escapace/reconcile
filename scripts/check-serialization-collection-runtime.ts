import assert from 'node:assert/strict'
import { map, set } from '../src/serialization/facets/collection'
import type { DecodeContext } from '../src/serialization/contracts'
import type { Oracle } from './lean-oracle'

interface Request {
  failAt: number | null
  map: boolean
  values: number[]
}
interface Response {
  entries: Array<[number, number]> | number[]
  error: number | null
  reads: number[]
}

function requests(): Request[] {
  const result: Request[] = []
  const add = (isMap: boolean, values: number[]) => {
    result.push({ failAt: null, map: isMap, values })
    for (let failAt = 0; failAt < values.length; failAt++)
      result.push({ failAt, map: isMap, values })
  }
  add(true, [])
  add(false, [])
  add(true, [14, 14, 15, 15, 14, 16, 16, 5])
  add(true, [4, 1, 5, 2, 12, 9, 4, 10, 6, 5])
  add(true, [11, 11, 12, 16, 11, 5])
  add(false, [14, 16, 15, 14, 4, 5, 4, 6])
  const all = Array.from({ length: 17 }, (_, index) => index)
  add(true, all.flatMap((key) => [key, key]).concat(all.flatMap((key) => [key, 5])))
  add(false, all.concat(all.toReversed()))
  for (let seed = 0; seed < 12; seed++) {
    const values = Array.from({ length: seed * 2 }, (_, index) => (index * 7 + seed) % 17)
    add(true, values)
    add(false, values)
  }
  return result
}

// Codes distinguish values by Object.is; only native key projection merges -0/+0.
// 14/15 are distinct equal objects, and 16 is the actual destination collection.
function domain(target: unknown): unknown[] {
  return [
    undefined,
    null,
    false,
    true,
    NaN,
    -0,
    0,
    Infinity,
    -Infinity,
    1,
    -1,
    0n,
    'a',
    'b',
    {},
    {},
    target,
  ]
}

function project(values: unknown[], value: unknown): number {
  const index = values.findIndex((candidate) => Object.is(candidate, value))
  assert.notEqual(index, -1, 'native result outside the finite bridge domain')
  return index
}

function contextFor(
  request: Request,
  values: unknown[],
  reads: number[],
  failure: Error,
): DecodeContext {
  return {
    checkedShapes: new Set(),
    nodes: [],
    output: [],
    owners: new Set(),
    shapes: [],
    read(token) {
      assert.equal(typeof token, 'number')
      const index = token as number
      assert(Number.isInteger(index) && index >= 0 && index < request.values.length)
      reads.push(index)
      if (index === request.failAt) throw failure
      return values[request.values[index]]
    },
  }
}

function projectedEntries(
  isMap: boolean,
  target: Map<unknown, unknown> | Set<unknown>,
  values: unknown[],
): Response['entries'] {
  return isMap
    ? [...(target as Map<unknown, unknown>)].map(([key, value]): [number, number] => [
        project(values, key),
        project(values, value),
      ])
    : [...(target as Set<unknown>)].map((value) => project(values, value))
}

function check(request: Request, expected: Response): void {
  const facet = request.map ? map : set
  const row = [request.map ? 4 : 5, ...request.values.map((_, index) => index)]
  const reads: number[] = []
  const failure = new Error('read sentinel')
  const empty = contextFor(request, [], reads, failure)
  const target = facet.allocate(row, empty) as Map<unknown, unknown> | Set<unknown>
  const values = domain(target)
  const context = contextFor(request, values, reads, failure)
  if (expected.error === null) facet.fill!(row, target, context)
  else
    assert.throws(
      () => facet.fill!(row, target, context),
      (error) => error === failure,
    )
  const entries = projectedEntries(request.map, target, values)
  assert.deepEqual(reads, expected.reads, 'every occurrence through the first failed read')
  assert.deepEqual(
    entries,
    expected.entries,
    'ordered native contents including partial failure state',
  )
  assert.equal(expected.error, request.failAt)
}

/** Calls actual production facets; Lean independently computes ordered fold/read prefixes. */
export async function checkSerializationCollectionRuntime(oracle: Oracle): Promise<void> {
  const cases = requests()
  const responses = JSON.parse(
    await oracle('SerializationCollection', [], { input: JSON.stringify(cases) }),
  ) as Response[]
  assert.equal(responses.length, cases.length)
  for (let index = 0; index < cases.length; index++) check(cases[index], responses[index])
  console.log(`Collection Lean/native facet bridge: ${cases.length} success/error traces`)
}
