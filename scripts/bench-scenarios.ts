import { Bench } from 'tinybench'
import {
  createContextRuntimeProduceImmerBenchmarks,
  createContextRuntimeReconcileBenchmarks,
  createContextRuntimeReconcilePlainObjectBenchmarks,
  createContextRuntimeSnapshotBenchmarks,
} from '../perf/scenarios'

function createBenchmark(name: string, tasks: Record<string, () => void>): Bench {
  // Match the frozen Vitest 4 declarations and Tinybench 2's 500 ms minimum.
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

// Construct each fixture only when its suite is about to run.
export function* createBenchmarks(): Generator<Bench, undefined> {
  const produce = createContextRuntimeProduceImmerBenchmarks()
  yield createBenchmark('produce vs immer shared draft surface', {
    'immer produce': produce.immerBatch,
    'produce': produce.produceBatch,
  })

  const reconcile = createContextRuntimeReconcileBenchmarks()
  yield createBenchmark('reconcile', {
    'detached clone reference': reconcile.baselineReconcileBatch,
    'reconcile': reconcile.runtimeReconcileBatch,
  })

  const plainObject = createContextRuntimeReconcilePlainObjectBenchmarks()
  yield createBenchmark('reconcilePlainObject', {
    'detached clone reference': plainObject.baselineReconcilePlainObjectBatch,
    'reconcilePlainObject': plainObject.runtimeReconcilePlainObjectBatch,
  })

  const snapshot = createContextRuntimeSnapshotBenchmarks()
  yield createBenchmark('snapshot', {
    baseline: snapshot.baselineSnapshotBatch,
    snapshot: snapshot.runtimeSnapshotBatch,
  })
}
