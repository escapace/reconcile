/**
 * The workloads every `pnpm bench` subcommand measures, named once. `snapshot`, `reconcile`,
 * `reconcile-plain-object` and `produce` are the frozen `perf/` workloads; `serialize` and
 * `deserialize` run the six serialization graphs below, from value to JSON text and back. These
 * six make the default round. The small round's ten run each function on a flat object of 1 and
 * of 16 keys (`smallOperation`); they are frozen as the `perf/` workloads are. An operation is one
 * call of the function.
 */

import type { deserialize, produce, reconcile, serialize, snapshot } from '../src/index'

/** The default round's scenarios. */
export const defaultScenarioNames = [
  'snapshot',
  'reconcile',
  'reconcile-plain-object',
  'produce',
  'serialize',
  'deserialize',
] as const

/** The small round's scenarios: each function on a flat object of 1 and of 16 keys. */
export const smallScenarioNames = [
  'snapshot-1',
  'snapshot-16',
  'reconcile-1',
  'reconcile-16',
  'produce-1',
  'produce-16',
  'serialize-1',
  'serialize-16',
  'deserialize-1',
  'deserialize-16',
] as const
export type SmallScenarioName = (typeof smallScenarioNames)[number]

export const scenarioNames = [...defaultScenarioNames, ...smallScenarioNames] as const
export type ScenarioName = (typeof scenarioNames)[number]

/** The scenarios of each standard round. */
export const rounds = {
  default: defaultScenarioNames,
  small: smallScenarioNames,
} as const satisfies Record<string, readonly ScenarioName[]>

/**
 * The serialization API of a source tree. Trees from before serialization export neither
 * function and reject the scenarios.
 */
export interface SerializationPorts {
  readonly deserialize?: typeof deserialize
  readonly serialize?: typeof serialize
}

/** The API of a source tree the small workloads call. */
export interface WorkloadPorts extends SerializationPorts {
  readonly produce?: typeof produce
  readonly reconcile?: typeof reconcile
  readonly snapshot?: typeof snapshot
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

/** A flat object of `size` keys `k0`, `k1`, … holding the given numbers. */
const flat = (size: number, value: (index: number) => number): Record<string, number> =>
  Object.fromEntries(Array.from({ length: size }, (_, index) => [`k${index}`, value(index)]))

/** The function a tree exports, or an error naming the scenario that needs it. */
function port<T>(value: T | undefined, scenario: string): T {
  if (value === undefined) throw new Error(`This source tree cannot run ${scenario}.`)
  return value
}

/** One operation of a workload, and a check of its latest result. */
export interface Operation {
  readonly run: () => void
  readonly validate: () => void
}

/** The functions the small workloads call. */
export type FlatFunction = 'deserialize' | 'produce' | 'reconcile' | 'serialize' | 'snapshot'

/** One workload per function, on a flat object of `size` keys. */
const flatWorkloads: Record<FlatFunction, (ports: WorkloadPorts, size: number) => Operation> = {
  deserialize: (ports, size) => {
    const { decode, encode } = textCodec(ports)
    const text = encode(flat(size, (index) => index))
    let last: unknown
    return {
      run: () => {
        last = decode(text)
      },
      validate: () => {
        if (encode(last) !== text) throw new Error('deserialize returned a different value')
      },
    }
  },
  // Rotates recipes that change nothing, one key and every key.
  produce: (ports, size) => {
    const produceValue = port(ports.produce, 'produce')
    const keys = Object.keys(flat(size, () => 0))
    const input = flat(size, () => 0)
    let turn = 0
    let last: Record<string, number> = input
    return {
      run: () => {
        const phase = turn++ % 3
        last = produceValue(input, (draft) => {
          if (phase === 0) draft.k0 = 0
          else if (phase === 1) draft.k0 = turn
          else for (const key of keys) draft[key] = turn
          return draft
        })
      },
      validate: () => {
        const changed = (turn - 1) % 3 !== 0
        if (
          input.k0 !== 0 ||
          (last === input) === changed ||
          (changed && last.k0 !== turn) ||
          Object.keys(last).join() !== keys.join()
        )
          throw new Error('produce returned an unexpected result')
      },
    }
  },
  // Updates one object in place, from the previous value: nothing, one key, one key back, every
  // key, every key back.
  reconcile: (ports, size) => {
    const reconcileValue = port(ports.reconcile, 'reconcile')
    const nexts = [
      flat(size, () => 0),
      flat(size, () => 0),
      flat(size, (index) => Number(index === 0)),
      flat(size, () => 0),
      flat(size, () => 2),
    ]
    const current = flat(size, () => 2)
    let turn = 0
    let last: unknown
    return {
      run: () => {
        last = reconcileValue(current, nexts[turn++ % nexts.length])
      },
      validate: () => {
        const expected = nexts[(turn - 1) % nexts.length]
        if (last !== current || JSON.stringify(current) !== JSON.stringify(expected))
          throw new Error('reconcile did not update the object in place')
      },
    }
  },
  serialize: (ports, size) => {
    const { encode } = textCodec(ports)
    const value = flat(size, (index) => index)
    const text = encode(value)
    let last: unknown
    return {
      run: () => {
        last = encode(value)
      },
      validate: () => {
        if (last !== text) throw new Error('serialize returned different text')
      },
    }
  },
  snapshot: (ports, size) => {
    const snapshotValue = port(ports.snapshot, 'snapshot')
    const input = flat(size, (index) => index)
    let last: unknown
    return {
      run: () => {
        last = snapshotValue(input)
      },
      validate: () => {
        if (last === input || JSON.stringify(last) !== JSON.stringify(input))
          throw new Error('snapshot returned an unexpected copy')
      },
    }
  },
}

/** One function's workload on a flat object of `size` keys; the `diag-tiny-*` diagnostics scale
 * it with their size. */
export function flatOperation(ports: WorkloadPorts, name: FlatFunction, size: number): Operation {
  return flatWorkloads[name](ports, size)
}

/** One operation of a small workload, `<function>-<keys>`. */
export function smallOperation(ports: WorkloadPorts, scenario: SmallScenarioName): Operation {
  const separator = scenario.lastIndexOf('-')
  return flatOperation(
    ports,
    scenario.slice(0, separator) as FlatFunction,
    Number(scenario.slice(separator + 1)),
  )
}

/** Replaces `--round <name>` with its scenarios as `--scenario` arguments. */
export function expandRound(arguments_: readonly string[]): string[] {
  const index = arguments_.indexOf('--round')
  if (index === -1) return [...arguments_]
  const name = arguments_[index + 1]
  if (name !== 'default' && name !== 'small')
    throw new Error(`Unknown round ${String(name)}; choose default or small.`)
  return [
    ...arguments_.slice(0, index),
    ...arguments_.slice(index + 2),
    ...rounds[name].flatMap((scenario) => ['--scenario', scenario]),
  ]
}
