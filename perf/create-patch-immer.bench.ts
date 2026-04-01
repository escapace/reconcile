import { bench, describe } from 'vitest'

import { createContextRuntimeCreatePatchImmerBenchmarks } from './scenarios'

const { createPatchBatch, immerBatch } = createContextRuntimeCreatePatchImmerBenchmarks()

describe('createPatch vs immer shared draft surface', () => {
  bench('immer produce', immerBatch, {
    iterations: 500,
    warmupIterations: 5,
    warmupTime: 100,
  })

  bench('createPatch', createPatchBatch, {
    iterations: 500,
    warmupIterations: 5,
    warmupTime: 100,
  })
})
