import { bench, describe } from 'vitest'

import { BATCH_SIZE, createContextRuntimeProduceImmerBenchmarks } from './scenarios'

const { immerBatch, produceBatch } = createContextRuntimeProduceImmerBenchmarks()

describe('produce vs immer shared draft surface', () => {
  bench(`immer produce (${BATCH_SIZE} updates/batch)`, immerBatch, {
    iterations: 500,
    warmupIterations: 5,
    warmupTime: 100,
  })

  bench(`produce (${BATCH_SIZE} updates/batch)`, produceBatch, {
    iterations: 500,
    warmupIterations: 5,
    warmupTime: 100,
  })
})
