import { assert, it } from 'vitest'
import { closeRequirements, RequirementClosure } from '../graph/requirements'
import { randomSource } from './fixtures/public-api-fuzz'

it('keeps object facts distinct while advancing a live activation iterator', () => {
  const left = { value: 0 }
  const right = { value: 0 }
  const parent = {}
  const closure = new RequirementClosure<object>()
  closure.imply(left, parent)
  closure.require(right)
  assert.isFalse(closure.facts.has(left))
  assert.isFalse(closure.facts.has(parent))
  const iterator = closure.facts.values()
  assert.strictEqual(iterator.next().value, right)
  closure.require(left)
  assert.strictEqual(iterator.next().value, left)
  assert.strictEqual(iterator.next().value, parent)
  assert.isTrue(iterator.next().done)
})

it('computes the least closed fact set across cycles and repeated seeds', () => {
  assert.deepEqual(
    [...closeRequirements([0, 0], [[1, 2], [3], [3], [0], [4]])].sort(
      (left, right) => left - right,
    ),
    [0, 1, 2, 3],
  )
  assert.deepEqual([...closeRequirements([], [[1], [0]])], [])
  const random = randomSource(31_981, 8).next
  for (let test = 0; test < 200; test += 1) {
    const size = 1 + random(7)
    const seeds = [random(size), random(size)]
    const implications = Array.from({ length: size }, () =>
      Array.from({ length: random(3) }, () => random(size)),
    )
    const closed = closeRequirements(seeds, implications)
    assertLeastClosure(size, seeds, implications, closed)
    assertClosed(seeds, implications, closed)
  }
})

// Every fact set that contains the seeds and is closed under the implications,
// enumerated as a bit mask, must contain the computed closure.
function assertLeastClosure(
  size: number,
  seeds: number[],
  implications: number[][],
  closed: ReadonlySet<number>,
): void {
  for (let mask = 0; mask < 2 ** size; mask += 1) {
    const contains = (fact: number): boolean => (mask & (1 << fact)) !== 0
    if (!seeds.every(contains)) continue
    if (implications.some((next, fact) => contains(fact) && !next.every(contains))) continue
    for (const fact of closed) assert.isTrue(contains(fact))
  }
}

function assertClosed(
  seeds: number[],
  implications: number[][],
  closed: ReadonlySet<number>,
): void {
  for (const fact of seeds) assert.isTrue(closed.has(fact))
  for (const fact of closed) for (const next of implications[fact]) assert.isTrue(closed.has(next))
}

it('closes late implications and seeds identically at every discovery prefix', () => {
  for (let graph = 0; graph < 512; graph += 1) {
    for (const seedsFirst of [false, true]) {
      checkDiscoveryPrefixes(graph, seedsFirst)
    }
  }
})

function checkDiscoveryPrefixes(graph: number, seedsFirst: boolean): void {
  const closure = new RequirementClosure()
  const edges: Array<[number, number]> = []
  let seeds = 0
  const check = (): void => {
    const expected = closedMask(seeds, edges)
    assert.deepEqual(
      [...closure.facts].sort((left, right) => left - right),
      [0, 1, 2].filter((id) => (expected & (1 << id)) !== 0),
    )
  }
  const seed = (id: number): void => {
    seeds |= 1 << id
    closure.require(id)
    check()
  }
  if (seedsFirst) seed(0)
  for (let index = 0; index < 9; index += 1) {
    if ((graph & (1 << index)) === 0) continue
    const from = Math.floor(index / 3)
    const to = index % 3
    edges.push([from, to])
    closure.imply(from, to)
    check()
  }
  if (!seedsFirst) seed(0)
  seed(1)
  closure.imply(0, 2)
  edges.push([0, 2])
  check()
  seed(0)
}

// Independent fixed point: the seed mask extended along edges until it stops changing.
function closedMask(seeds: number, edges: ReadonlyArray<readonly [number, number]>): number {
  let expected = seeds
  for (let previous = -1; previous !== expected;) {
    previous = expected
    for (const [from, to] of edges) if ((expected & (1 << from)) !== 0) expected |= 1 << to
  }
  return expected
}

it('preserves first-discovery insertion order across duplicate seeds and cyclic consequences', () => {
  assert.deepEqual([...closeRequirements([2, 0, 2], [[3, 1], [2], [1, 3, 1], [0]])], [2, 0, 1, 3])
})

it('skips settled consequences without losing future propagation or live iteration order', () => {
  const closure = new RequirementClosure()
  closure.require(2)
  closure.imply(0, 2)
  closure.imply(0, 1)
  closure.imply(1, 2)
  closure.imply(1, 3)
  closure.imply(3, 0)
  closure.require(0)
  assert.deepEqual([...closure.facts], [2, 0, 1, 3])
  const visited: number[] = []
  for (const fact of closure.facts) {
    visited.push(fact)
    if (fact === 1) {
      closure.imply(1, 2)
      closure.imply(1, 4)
      closure.imply(4, 5)
    }
  }
  assert.deepEqual(visited, [2, 0, 1, 3, 4, 5])
  closure.imply(5, 5)
  closure.require(0)
  assert.deepEqual([...closure.facts], visited)
})

it('preserves existing insertion order when known facts gain new implications', () => {
  const closure = new RequirementClosure()
  closure.imply(2, 3)
  closure.imply(3, 2)
  closure.require(0)
  closure.require(1)
  closure.imply(0, 2)
  assert.deepEqual([...closure.facts], [0, 1, 2, 3])
  closure.imply(1, 2)
  closure.require(0)
  assert.deepEqual([...closure.facts], [0, 1, 2, 3])
  closure.imply(3, 4)
  assert.deepEqual([...closure.facts], [0, 1, 2, 3, 4])
})
