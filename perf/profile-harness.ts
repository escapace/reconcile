import { writeFileSync } from 'node:fs'
import { Session } from 'node:inspector/promises'

import { BATCH_SIZE } from './config'
import {
  createContextRuntimeProduceImmerBenchmarks,
  createContextRuntimeReconcileBenchmarks,
  createContextRuntimeReconcilePlainObjectBenchmarks,
  createContextRuntimeSnapshotBenchmarks,
} from './scenarios'

const [scenario, countArgument, warmupArgument = '0', mode, outputPath, intervalArgument] =
  process.argv.slice(2)
const batchCount = Number(countArgument)
const warmupCount = Number(warmupArgument)
if (
  scenario === undefined ||
  !Number.isInteger(batchCount) ||
  batchCount < 1 ||
  !Number.isInteger(warmupCount) ||
  warmupCount < 0
) {
  throw new Error(
    'Usage: profile-harness.ts <scenario> <batches> [warmupBatches] [cpu|heap outputPath interval]',
  )
}

const profileScenarios: Record<string, () => () => void> = {
  'produce': () => createContextRuntimeProduceImmerBenchmarks().produceBatch,
  'reconcile': () => createContextRuntimeReconcileBenchmarks().runtimeReconcileBatch,
  'reconcile-plain-object': () =>
    createContextRuntimeReconcilePlainObjectBenchmarks().runtimeReconcilePlainObjectBatch,
  'snapshot': () => createContextRuntimeSnapshotBenchmarks().runtimeSnapshotBatch,
}
const run = profileScenarios[scenario]?.()
if (run === undefined) throw new Error(`Unknown scenario: ${scenario}`)
for (let index = 0; index < warmupCount; index += 1) run()

const session = new Session()
if (mode !== undefined) {
  const interval = Number(intervalArgument)
  if (
    (mode !== 'cpu' && mode !== 'heap') ||
    outputPath === undefined ||
    !Number.isInteger(interval) ||
    interval < 1
  )
    throw new Error('Profiling requires cpu|heap, an output path, and a positive interval.')
  session.connect()
  if (mode === 'cpu') {
    await session.post('Profiler.enable')
    await session.post('Profiler.setSamplingInterval', { interval })
    await session.post('Profiler.start')
  } else {
    await session.post('HeapProfiler.startSampling', {
      includeObjectsCollectedByMajorGC: true,
      includeObjectsCollectedByMinorGC: true,
      samplingInterval: interval,
    })
  }
}
for (let index = 0; index < batchCount; index += 1) run()
if (mode !== undefined) {
  const { profile } =
    mode === 'cpu'
      ? await session.post('Profiler.stop')
      : await session.post('HeapProfiler.stopSampling')
  session.disconnect()
  writeFileSync(outputPath, JSON.stringify(profile))
}
console.log(
  `Profiled ${scenario}: ${batchCount * BATCH_SIZE} operations after ${warmupCount} warmup batches`,
)
