/**
 * `pnpm bench run`: Tinybench tables for every scenario against a reference (`structuredClone`,
 * a detached clone, Immer or `JSON`). A frozen-workload sample is one batch of `BATCH_SIZE`
 * operations; a serialization sample is one call on one workload. It orients; it does not decide.
 *
 * Usage: pnpm bench run [--scenario <name>]...
 */

import path from 'node:path'
import { parseArgs } from 'node:util'
import { Bench } from 'tinybench'
import {
  BATCH_SIZE,
  createContextRuntimeProduceImmerBenchmarks,
  createContextRuntimeReconcileBenchmarks,
  createContextRuntimeReconcilePlainObjectBenchmarks,
  createContextRuntimeSnapshotBenchmarks,
} from '../perf/scenarios'
import { deserialize, serialize } from '../src/index'
import {
  selectScenarios,
  type ScenarioName,
  scenarioNames,
  serializationFixtures,
} from './bench-workloads'

function createBenchmark(name: string, tasks: Record<string, () => void>): Bench {
  // At least 500 samples and 500 ms per task, after five warmup samples and 100 ms.
  const benchmark = new Bench({
    concurrency: null,
    iterations: 500,
    name,
    throws: true,
    time: 500,
    warmup: true,
    warmupIterations: 5,
    warmupTime: 100,
  })
  for (const [taskName, run] of Object.entries(tasks)) {
    benchmark.add(taskName, run, { async: false })
  }
  return benchmark
}

/** Builds the serialization workloads at most once per `createBenchmarks` call. */
function lazyFixtures(): () => ReturnType<typeof serializationFixtures> {
  let fixtures: ReturnType<typeof serializationFixtures> | undefined
  return () => (fixtures ??= serializationFixtures({ deserialize, serialize }))
}

function jsonReference(fixtures: ReturnType<typeof serializationFixtures>): object {
  return fixtures.find(({ name }) => name === 'json-1000')!.value
}

function suiteFactories(
  fixtures: () => ReturnType<typeof serializationFixtures>,
): Record<ScenarioName, () => Bench> {
  return {
    'deserialize': () => {
      const jsonText = JSON.stringify(jsonReference(fixtures()))
      const tasks: Record<string, () => void> = {
        'JSON.parse json-1000 (reference)': () => JSON.parse(jsonText) as unknown,
      }
      for (const { name, text } of fixtures())
        tasks[name] = () => deserialize(JSON.parse(text), { maxBytes: Infinity })
      return createBenchmark('deserialize', tasks)
    },
    'produce': () => {
      const produce = createContextRuntimeProduceImmerBenchmarks()
      return createBenchmark('produce vs immer shared draft surface', {
        'immer produce': produce.immerBatch,
        'produce': produce.produceBatch,
      })
    },
    'reconcile': () => {
      const reconcile = createContextRuntimeReconcileBenchmarks()
      return createBenchmark('reconcile', {
        'detached clone reference': reconcile.baselineReconcileBatch,
        'reconcile': reconcile.runtimeReconcileBatch,
      })
    },
    'reconcile-plain-object': () => {
      const plainObject = createContextRuntimeReconcilePlainObjectBenchmarks()
      return createBenchmark('reconcilePlainObject', {
        'detached clone reference': plainObject.baselineReconcilePlainObjectBatch,
        'reconcilePlainObject': plainObject.runtimeReconcilePlainObjectBatch,
      })
    },
    'serialize': () => {
      const json = jsonReference(fixtures())
      const tasks: Record<string, () => void> = {
        'JSON.stringify json-1000 (reference)': () => JSON.stringify(json),
      }
      for (const { name, value } of fixtures()) tasks[name] = () => JSON.stringify(serialize(value))
      return createBenchmark('serialize', tasks)
    },
    'snapshot': () => {
      const snapshot = createContextRuntimeSnapshotBenchmarks()
      return createBenchmark('snapshot', {
        'snapshot': snapshot.runtimeSnapshotBatch,
        'structuredClone reference': snapshot.baselineSnapshotBatch,
      })
    },
  }
}

/** Yields each selected scenario in library order, building its fixtures just before it runs. */
export function* createBenchmarks(
  selected: readonly ScenarioName[] = scenarioNames,
): Generator<{ bench: Bench; scenario: ScenarioName }, undefined> {
  const factories = suiteFactories(lazyFixtures())
  for (const scenario of scenarioNames)
    if (selected.includes(scenario)) yield { bench: factories[scenario](), scenario }
}

export function selectedScenarios(argv: string[]): ScenarioName[] {
  const { values } = parseArgs({
    args: argv,
    options: { scenario: { multiple: true, type: 'string' } },
  })
  return selectScenarios(values.scenario)
}

function run(argv: string[]): void {
  if (argv.includes('--help') || argv.includes('-h')) {
    console.log(
      `Usage: pnpm bench run [--scenario <name>]...\nScenarios: ${scenarioNames.join(', ')}`,
    )
    return
  }
  console.log(
    `Tinybench: a frozen-workload sample is one batch of ${BATCH_SIZE} operations; ` +
      'a serialization sample is one call.',
  )
  for (const { bench } of createBenchmarks(selectedScenarios(argv))) {
    console.log(`\n${bench.name}`)
    for (const task of bench.runSync())
      if (task.result.state !== 'completed')
        throw new Error(`Benchmark did not complete: ${bench.name} / ${task.name}`, {
          cause: task.result,
        })
    console.table(bench.table())
  }
}

if (process.argv[1] !== undefined && path.resolve(process.argv[1]) === import.meta.filename)
  run(process.argv.slice(2))
