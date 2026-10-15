import { BATCH_SIZE } from '../perf/config'
import { createBenchmarks } from './bench-scenarios'

console.log(`Tinybench: each sample is one batch of ${BATCH_SIZE} operations`)
for (const benchmark of createBenchmarks()) {
  console.log(`\n${benchmark.name}`)
  for (const task of benchmark.runSync()) {
    if (task.result.state !== 'completed') {
      throw new Error(`Benchmark did not complete: ${benchmark.name} / ${task.name}`, {
        cause: task.result,
      })
    }
  }
  console.table(benchmark.table())
}
