/**
 * The workloads every `pnpm bench` subcommand measures, named once. `snapshot`, `reconcile`,
 * `reconcile-plain-object` and `produce` are the frozen `perf/` workloads; `serialize` and
 * `deserialize` run the six serialization graphs below, from value to JSON text and back. An
 * operation is one call of the function.
 */

import type * as Frozen from '../perf/scenarios'
import type { deserialize, serialize } from '../src/index'

export const scenarioNames = [
  'snapshot',
  'reconcile',
  'reconcile-plain-object',
  'produce',
  'serialize',
  'deserialize',
] as const
export type ScenarioName = (typeof scenarioNames)[number]

function isScenarioName(name: string): name is ScenarioName {
  return (scenarioNames as readonly string[]).includes(name)
}

/** Validates `--scenario` values and returns them in library order; none selects every one. */
export function selectScenarios(selected: readonly string[] | undefined): ScenarioName[] {
  for (const name of selected ?? [])
    if (!isScenarioName(name))
      throw new Error(`Unknown scenario ${name}; choose from ${scenarioNames.join(', ')}`)
  return scenarioNames.filter((name) => selected?.includes(name) ?? true)
}

/**
 * The serialization API of a source tree. Trees from before serialization export neither
 * function and reject the scenarios.
 */
export interface SerializationPorts {
  readonly deserialize?: typeof deserialize
  readonly serialize?: typeof serialize
}

/**
 * A tree's serialization from value to JSON text and back: `JSON.stringify(serialize(value))` and
 * `deserialize(JSON.parse(text), { maxBytes })`.
 */
export function textCodec(
  ports: SerializationPorts,
  maxBytes = Infinity,
): {
  decode: (text: string) => unknown
  encode: (value: unknown) => string
} {
  const { deserialize, serialize } = ports
  if (serialize !== undefined && deserialize !== undefined)
    return {
      decode: (text) => deserialize(JSON.parse(text), { maxBytes }),
      encode: (value) => JSON.stringify(serialize(value)),
    }
  throw new Error('This source tree has no serialization API; serialization scenarios need it.')
}

const deep = (depth: number): object => {
  let value: object = { end: true }
  for (let level = 0; level < depth; level += 1) value = { next: value }
  return value
}

/**
 * Graphs for the `serialize` and `deserialize` scenarios: plain JSON, values JSON cannot carry,
 * shared references, cycles, binary data and deep nesting. Each factory builds a fresh graph.
 */
const serializationWorkloads = {
  'binary-64k': (): object => {
    const buffer = new ArrayBuffer(65_536)
    new Uint8Array(buffer).fill(42)
    return { buffer, data: new DataView(buffer, 32, 8000), view: new Uint8Array(buffer, 8, 4096) }
  },
  'cycle-300': (): object => {
    const nodes = Array.from({ length: 300 }, (_, index): { index: number; next?: object } => ({
      index,
    }))
    for (const [index, node] of nodes.entries()) node.next = nodes[(index + 1) % nodes.length]
    return nodes
  },
  'dag-2000': (): object => {
    const pool = Array.from({ length: 20 }, (_, id) => ({ id, label: `shared-${id}` }))
    return Array.from({ length: 2000 }, (_, index) => ({ index, value: pool[index % 20] }))
  },
  'deep-200': (): object => deep(200),
  'json-1000': (): object =>
    Array.from({ length: 1000 }, (_, id) => ({
      active: id % 2 === 0,
      id,
      name: `item-${id}`,
      values: [id, id + 1, id + 2],
    })),
  'rich': (): object => {
    const key = {}
    const map = new Map<unknown, unknown>()
    const set = new Set<unknown>()
    map.set(key, set)
    set.add(map)
    const date = new Date(1234)
    const buffer = new ArrayBuffer(32)
    new Uint8Array(buffer).set([1, 2, 3, 4])
    const view = new Uint8Array(buffer, 2, 7)
    return {
      binary: { again: view, buffer, data: new DataView(buffer, 3, 5), view },
      collections: { again: map, key, map, set },
      dates: [date, date, new Date(Number.NaN)],
      values: [undefined, Number.NaN, Infinity, -Infinity, -0, 12n, null, true, ''],
    }
  },
} satisfies Record<string, () => object>

type SerializationWorkload = keyof typeof serializationWorkloads
const workloadCount = Object.keys(serializationWorkloads).length

/** Builds every workload once, with its text, after checking that the text round-trips. */
export function serializationFixtures(
  ports: SerializationPorts,
): Array<{ name: string; text: string; value: object }> {
  const { decode, encode } = textCodec(ports)
  return (Object.keys(serializationWorkloads) as SerializationWorkload[]).map((name) => {
    const value = serializationWorkloads[name]()
    const text = encode(value)
    if (encode(decode(text)) !== text) throw new Error(`Serialization round trip changed ${name}`)
    return { name, text, value }
  })
}

/**
 * One serialization operation per call of `run`, rotating through the six workloads so that
 * each weighs the same: `serialize` from value to JSON text, `deserialize` from JSON text to
 * value. `validate` checks the latest result against the fixture.
 */
export function serializationOperation(
  ports: SerializationPorts,
  scenario: 'deserialize' | 'serialize',
  maxBytes = Infinity,
): { run: () => void; validate: () => void } {
  const fixtures = serializationFixtures(ports)
  const { decode, encode } = textCodec(ports, maxBytes)
  let turn = 0
  let last: unknown
  return scenario === 'deserialize'
    ? {
        run: () => {
          last = decode(fixtures[turn++ % fixtures.length].text)
        },
        validate: () => {
          if (encode(last) !== fixtures[(turn - 1) % fixtures.length].text)
            throw new Error('deserialize returned a different graph')
        },
      }
    : {
        run: () => {
          last = encode(fixtures[turn++ % fixtures.length].value)
        },
        validate: () => {
          if (last !== fixtures[(turn - 1) % fixtures.length].text)
            throw new Error('serialize returned different text')
        },
      }
}

/**
 * Batch factories of one source tree for `pnpm bench compare`: a frozen batch is
 * `BATCH_SIZE` operations of its workload, and a serialization batch is one operation on each
 * serialization workload.
 */
export function createBatches(
  scenarios: typeof Frozen,
  ports: SerializationPorts,
): Record<ScenarioName, () => () => void> {
  const serialization = (scenario: 'deserialize' | 'serialize') => () => {
    const { run } = serializationOperation(ports, scenario)
    return () => {
      for (let index = 0; index < workloadCount; index += 1) run()
    }
  }
  return {
    'deserialize': serialization('deserialize'),
    'serialize': serialization('serialize'),
    'produce': () => scenarios.createContextRuntimeProduceImmerBenchmarks().produceBatch,
    'reconcile': () => scenarios.createContextRuntimeReconcileBenchmarks().runtimeReconcileBatch,
    'reconcile-plain-object': () =>
      scenarios.createContextRuntimeReconcilePlainObjectBenchmarks()
        .runtimeReconcilePlainObjectBatch,
    'snapshot': () => scenarios.createContextRuntimeSnapshotBenchmarks().runtimeSnapshotBatch,
  }
}
