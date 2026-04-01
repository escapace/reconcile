import { bench, describe } from 'vitest'
import { createContextRuntimeReconcileBenchmarks } from './scenarios'

const { baselineReconcileBatch, runtimeReconcileBatch } = createContextRuntimeReconcileBenchmarks()

describe('reconcile', () => {
  bench(`baseline`, baselineReconcileBatch, {
    iterations: 500,
    warmupIterations: 5,
    warmupTime: 100,
  })
  bench(`reconcile`, runtimeReconcileBatch, {
    iterations: 500,
    warmupIterations: 5,
    warmupTime: 100,
  })
})
