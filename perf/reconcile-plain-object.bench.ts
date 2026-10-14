import { bench, describe } from 'vitest'
import { createContextRuntimeReconcilePlainObjectBenchmarks } from './scenarios'

const { baselineReconcilePlainObjectBatch, runtimeReconcilePlainObjectBatch } =
  createContextRuntimeReconcilePlainObjectBenchmarks()

describe('reconcilePlainObject', () => {
  bench(`detached clone reference`, baselineReconcilePlainObjectBatch, {
    iterations: 500,
    warmupIterations: 5,
    warmupTime: 100,
  })
  bench(`reconcilePlainObject`, runtimeReconcilePlainObjectBatch, {
    iterations: 500,
    warmupIterations: 5,
    warmupTime: 100,
  })
})
