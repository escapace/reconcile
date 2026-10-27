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

// Payload slots are node references into `values`; the output proxy records each resolved
// read. A failing occurrence is an out-of-range reference, rejected before it is read.
function contextFor(request: Request, values: unknown[], reads: number[]): DecodeContext {
  const output = new Proxy(values, {
    get(target, key, receiver) {
      if (typeof key === 'string' && /^\d+$/.test(key)) reads.push(Number(key))
      return Reflect.get(target, key, receiver) as unknown
    },
  })
  // Every slot node is already entered, so the bridge isolates resolution and the fold.
  // The control table holds only the collection's framed layout, at offset 1.
  const layout = layoutFor(request)
  return {
    control: [layout.length, ...layout],
    cursor: values.length,
    ends: [],
    // No size limit: the bridge traces resolution and the fold, not accounting.
    limit: Infinity,
    limited: false,
    maxBytes: Infinity,
    measuring: false,
    nodeLayouts: [],
    output,
    owned: 0,
    parameters: undefined,
    payloads: [],
    shapes: [],
    urls: 0,
    weights: undefined,
    words: 1,
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

// All slots are references; an empty payload lists no run.
function layoutFor(request: Request): number[] {
  const tag = request.map ? 4 : 5
  return request.values.length === 0 ? [tag] : [tag, 0]
}

// Fills through the production facet; a failing occurrence is recorded as attempted.
function fillTrace(
  facet: typeof map,
  request: Request,
  target: unknown,
  values: unknown[],
): number[] {
  // Slot i references the node at its own position; that node holds the value's code.
  const nodes = request.values.map((code) => values[code])
  const payload: unknown[] = request.values.map((_, index) => index)
  const reads: number[] = []
  const context = contextFor(request, nodes, reads)
  if (request.failAt === null) facet.fill!(payload, target, 1, context, values.length)
  else {
    payload[request.failAt] = nodes.length
    assert.throws(
      () => facet.fill!(payload, target, 1, context, values.length),
      (error: Error) => (error.cause as { reason?: string }).reason === 'reference',
    )
    reads.push(request.failAt)
  }
  return reads
}

function check(request: Request, expected: Response): void {
  const facet = request.map ? map : set
  const target = facet.allocate([], 1, contextFor(request, [], []), 0) as
    Map<unknown, unknown> | Set<unknown>
  const values = domain(target)
  const reads = fillTrace(facet, request, target, values)
  const entries = projectedEntries(request.map, target, values)
  assert.deepEqual(reads, expected.reads, 'every occurrence through the first failed read')
  assert.deepEqual(entries, expected.entries, 'ordered native contents; untouched on failure')
  assert.equal(expected.error, request.failAt)
}

/** Calls actual production facets; Lean independently computes ordered resolution and fold. */
export async function checkSerializationCollectionRuntime(oracle: Oracle): Promise<void> {
  const cases = requests()
  const responses = JSON.parse(
    await oracle('SerializationCollection', { input: JSON.stringify(cases) }),
  ) as Response[]
  assert.equal(responses.length, cases.length)
  for (let index = 0; index < cases.length; index++) check(cases[index], responses[index])
  console.log(`Collection Lean/native facet bridge: ${cases.length} success/error traces`)
}
