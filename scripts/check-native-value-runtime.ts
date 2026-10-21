// Native observations are supplied by JavaScript; Lean compares finite payload decisions.
import assert from 'node:assert/strict'
import { readFileSync } from 'node:fs'
import { capture } from '../src/publication/capture'
import { isNode } from '../src/graph/edge'
import type { Edge } from '../src/types'
import { builtinTypes, publicationTypes } from '../src/types/builtins'
import { OBJECT_KIND } from '../src/types/object'
import { snapshot } from '../src/snapshot'
import { produce } from '../src/produce'
import type { Oracle } from './lean-oracle'

interface Fixture {
  current: Payload
  desired: Payload
}
interface Payload {
  constructor: number
  entries: Array<[string, string]>
  kind: string
  values: string[]
}
interface Result {
  compatible: boolean
  entries: Array<[string, string]>
  published: boolean
  reusable: boolean
}
interface TemporalConstructor {
  from: (value: unknown) => object
}
const durationFields = [
  'years',
  'months',
  'weeks',
  'days',
  'hours',
  'minutes',
  'seconds',
  'milliseconds',
  'microseconds',
  'nanoseconds',
]

function construct(payload: Payload): object | undefined {
  if (payload.kind === 'URL') return new URL(payload.values[0])
  if (payload.kind === 'URLSearchParams') return new URLSearchParams(payload.entries)
  return constructTemporal(payload)
}

function constructTemporal(payload: Payload): object | undefined {
  const temporal = Reflect.get(globalThis, 'Temporal') as unknown as
    Partial<Record<string, TemporalConstructor>> | undefined
  const constructor = temporal?.[payload.kind]
  if (constructor === undefined) return undefined
  return constructor.from(
    payload.kind === 'Duration'
      ? Object.fromEntries(
          durationFields.map((field, index) => [field, Number(payload.values[index])]),
        )
      : payload.values[0],
  )
}

function observe(value: object, kind: string): Pick<Payload, 'entries' | 'values'> {
  if (kind === 'URL') return { entries: [], values: [(value as URL).href] }
  if (kind === 'URLSearchParams') return { entries: [...(value as URLSearchParams)], values: [] }
  if (kind === 'Duration')
    return { entries: [], values: durationFields.map((field) => String(Reflect.get(value, field))) }
  return { entries: [], values: [(value as { toString: () => string }).toString()] }
}

function checkGraph(value: object, kind: string) {
  const other = snapshot(value) as object
  const source = { again: value, other, value }
  const copy = snapshot(source) as typeof source
  assert.notEqual(copy.value, value)
  assert.equal(copy.value, copy.again)
  assert.notEqual(copy.other, copy.value)
  assert.deepEqual(observe(copy.value, kind), observe(value, kind))
  assert.equal(
    produce(source, (draft) => {
      void draft.value
      return draft
    }),
    source,
  )
}

/** Runs native facets at their own capture, publication and readback boundaries. */
function evaluateFacets(current: object, desired: object, kind: symbol, name: string): Result {
  const graph = capture(publicationTypes, desired)
  const node = graph.nodes[0]
  const policy = publicationTypes.policies[kind]
  const special = builtinTypes.specials[kind]
  assert.ok(special !== undefined)
  const compatible = publicationTypes.matches(kind, current) && policy.compatible(node, current)
  const reusable = special.equivalent(current, desired)
  const resolve = (edge: Edge): unknown => {
    if (!isNode(edge)) return edge.value
    assert.equal(name, 'URL')
    assert.equal(edge, node.edges[0])
    return (current as URL).searchParams
  }
  const published = compatible && policy.publish(node, current, resolve)
  if (published) {
    assert.equal(
      policy.matches(node, current, (value, edge) => value === resolve(edge)),
      true,
    )
    assert.deepEqual(observe(current, name), observe(desired, name))
  }
  return { compatible, entries: observe(current, name).entries, published, reusable }
}

/** Captures oracle labels before publication can mutate the native current value. */
function checkFixture(fixture: Fixture): { actual: Result; observed: Fixture } | undefined {
  const current = construct(fixture.current)
  const desired = construct(fixture.desired)
  if (current === undefined || desired === undefined) return undefined
  const kind = publicationTypes.recognize(desired)
  assert.ok(kind !== undefined, `Available ${fixture.desired.kind} must be registered`)
  assert.notEqual(kind, OBJECT_KIND, `Available ${fixture.desired.kind} must be registered`)
  const observed = {
    current: { ...fixture.current, ...observe(current, fixture.current.kind) },
    desired: { ...fixture.desired, ...observe(desired, fixture.desired.kind) },
  }
  const actual = evaluateFacets(current, desired, kind, fixture.desired.kind)
  checkGraph(desired, fixture.desired.kind)
  return { actual, observed }
}

/** Compares actual registered facets and native readback with the finite oracle. */
export async function checkNativeValueRuntime(oracle: Oracle): Promise<void> {
  const fixtures = JSON.parse(
    readFileSync('lean/fixtures/native-value-fixtures.json', 'utf8'),
  ) as Fixture[]
  const active: Fixture[] = []
  const actual: Result[] = []
  const skipped = new Set<string>()
  for (const fixture of fixtures) {
    const checked = checkFixture(fixture)
    if (checked === undefined) {
      skipped.add(fixture.desired.kind)
      continue
    }
    active.push(checked.observed)
    actual.push(checked.actual)
  }
  const expected = JSON.parse(
    await oracle('NativeValue', [], { input: JSON.stringify(active) }),
  ) as Result[]
  assert.deepEqual(actual, expected)
  console.log(
    `NativeValue: ${active.length} native facet/public API cases; skipped unavailable kinds: ${skipped.size === 0 ? 'none' : [...skipped].join(', ')}`,
  )
}
