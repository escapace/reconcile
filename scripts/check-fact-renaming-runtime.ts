import assert from 'node:assert/strict'
import { integerIn, jsonObject, oracleCorpus, type Oracle } from './lean-oracle'
import { RequirementClosure } from '../src/graph/requirements'

interface History {
  readonly actions: number[][]
  readonly mappedOrders: number[][]
  readonly orders: number[][]
  readonly queries: Array<boolean | null>
  readonly renamed: number[][]
  readonly size: number
}
interface Totals {
  cursorReads: number
  events: number
  queries: number
}

function labels(entry: unknown[], size: number): number[] {
  return entry.map((label: unknown) => integerIn(label, 0, size - 1))
}

/** Decodes one action: a query or requirement with one fact, or an implication with two. */
function action(entry: unknown, size: number): number[] {
  assert.ok(Array.isArray(entry) && entry.length <= 3)
  const kind = integerIn(entry[0], 0, 2)
  assert.equal(entry.length, kind === 2 ? 3 : 2)
  return [kind, ...labels(entry.slice(1), size)]
}

function order(entry: unknown, size: number): number[] {
  assert.ok(Array.isArray(entry) && entry.length <= size)
  return labels(entry, size)
}

function column(value: unknown, decode: (entry: unknown) => number[]): number[][] {
  assert.ok(Array.isArray(value) && value.length <= 512)
  return value.map((entry: unknown) => decode(entry))
}

function query(value: unknown): boolean | null {
  assert.ok(value === null || typeof value === 'boolean')
  return value
}

function decodeHistory(row: Record<string, unknown>): History {
  const size = integerIn(row.size, 0, 64)
  const actions = column(row.actions, (entry) => action(entry, size))
  const renamed = column(row.renamed, (entry) => action(entry, size))
  const orders = column(row.orders, (entry) => order(entry, size))
  const mappedOrders = column(row.mappedOrders, (entry) => order(entry, size))
  assert.ok(Array.isArray(row.queries))
  const queries = row.queries.map((value: unknown) => query(value))
  for (const values of [renamed, orders, mappedOrders, queries])
    assert.equal(values.length, actions.length)
  return { actions, mappedOrders, orders, queries, renamed, size }
}

const opaque = (): object =>
  new Proxy(
    {},
    {
      get() {
        throw new Error('Fact representation inspected an opaque identity')
      },
    },
  )

/** Distinct native facts: two forwarding proxies of one target, an opaque proxy, then functions. */
function factObjects(size: number): object[] {
  const owner = {}
  const left = new Proxy(owner, {})
  const right = new Proxy(owner, {})
  assert.notEqual(left, right)
  return Array.from({ length: size }, (_, id) =>
    id === 0 ? left : id === 1 ? right : id === 2 ? opaque() : () => undefined,
  )
}

function invoke<Fact>(
  closure: RequirementClosure<Fact>,
  input: number[],
  decode: (id: number) => Fact,
): boolean | null {
  if (input[0] === 0) return closure.facts.has(decode(input[1]))
  if (input[0] === 1) closure.require(decode(input[1]))
  else closure.imply(decode(input[1]), decode(input[2]))
  return null
}

/**
 * Reads one live `facts` iterator across the history: it opens at the first nonempty state,
 * advances on even steps and must finish exactly at the final order.
 */
function liveCursor(closure: RequirementClosure<object>, encode: (value: object) => number) {
  let iterator: Iterator<object, undefined> | undefined
  let position = 0
  let reads = 0
  const read = (expected: readonly number[]): void => {
    const next: IteratorResult<object, undefined> = iterator!.next()
    assert.ok(next.done !== true)
    assert.equal(encode(next.value), expected[position++])
    reads += 1
  }
  const due = (step: number, expected: readonly number[]): boolean =>
    iterator !== undefined && position < expected.length && step % 2 === 0
  return {
    finish(final: readonly number[] | undefined): number {
      if (iterator === undefined) return reads
      assert.ok(final !== undefined)
      while (position < final.length) read(final)
      assert.equal(iterator.next().done, true)
      return reads
    },
    step(step: number, expected: readonly number[]): void {
      if (iterator === undefined && closure.facts.size > 0) iterator = closure.facts.values()
      if (due(step, expected)) read(expected)
    },
  }
}

/** Replays one history over numeric and renamed native facts in lockstep. */
function replayHistory(index: number, history: History, totals: Totals): void {
  const objects = factObjects(history.size)
  const labelOf = new Map(objects.map((value, id) => [value, id]))
  const encode = (value: object): number => {
    const label = labelOf.get(value)
    assert.ok(label !== undefined)
    return label
  }
  const numeric = new RequirementClosure()
  const native = new RequirementClosure<object>()
  const cursor = liveCursor(native, encode)
  for (const [step, action] of history.actions.entries()) {
    assert.equal(action[0], history.renamed[step][0])
    assert.equal(
      invoke(numeric, action, (id) => id),
      history.queries[step],
    )
    assert.equal(
      invoke(native, history.renamed[step], (id) => objects[id]),
      history.queries[step],
    )
    assert.deepEqual([...numeric.facts], history.orders[step])
    assert.deepEqual(
      [...native.facts].map(encode),
      history.mappedOrders[step],
      `History ${index}, step ${step}`,
    )
    cursor.step(step, history.mappedOrders[step])
    totals.events += 1
    totals.queries += Number(action[0] === 0)
  }
  totals.cursorReads += cursor.finish(history.mappedOrders.at(-1))
}

/** An iterator that finished on an empty closure stays finished after a later admission. */
function checkFinishedIterator(): void {
  const owner = {}
  const left = new Proxy(owner, {})
  const right = new Proxy(owner, {})
  const closure = new RequirementClosure<object>()
  const finished = closure.facts.values()
  assert.equal(finished.next().done, true)
  closure.require(left)
  assert.equal(closure.facts.has(right), false)
  assert.equal(finished.next().done, true)
}

export async function checkFactRenamingRuntime(oracle: Oracle): Promise<void> {
  const lines = await oracleCorpus(oracle, 'FactRenaming', 41_069, 128 * 1024 * 1024)
  const totals: Totals = { cursorReads: 0, events: 0, queries: 0 }
  for (const [index, line] of lines.entries())
    replayHistory(index, decodeHistory(jsonObject(JSON.parse(line))), totals)
  checkFinishedIterator()
  console.log(
    `Fact-renaming bridge: ${lines.length} histories, ${totals.events} events, ${totals.queries} queries, ${totals.cursorReads} live cursor reads.`,
  )
}
