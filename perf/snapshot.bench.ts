import { bench, describe } from 'vitest'
import { createContextRuntimeSnapshotBenchmarks } from './scenarios'

const { baselineSnapshotBatch, runtimeSnapshotBatch } = createContextRuntimeSnapshotBenchmarks()

describe('snapshot', () => {
  bench(`baseline`, baselineSnapshotBatch, {
    iterations: 500,
    warmupIterations: 5,
    warmupTime: 100,
  })
  bench(`snapshot`, runtimeSnapshotBatch, {
    iterations: 500,
    warmupIterations: 5,
    warmupTime: 100,
  })
})
