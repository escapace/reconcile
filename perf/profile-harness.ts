import { BATCH_SIZE } from './config'
import {
  createContextRuntimeCreatePatchImmerBenchmarks,
  createContextRuntimeReconcileBenchmarks,
  createContextRuntimeReconcilePlainObjectBenchmarks,
  createContextRuntimeSnapshotBenchmarks,
} from './scenarios'

const [scenario, batchCountArgument] = process.argv.slice(2)
const batchCount = Number(batchCountArgument)

if (scenario === undefined || scenario === '' || !Number.isFinite(batchCount)) {
  console.error('Usage: profile-harness.ts <scenario> <batchCount>')
  process.exit(1)
}

const runBatch = (callback: () => void, count: number): void => {
  for (let index = 0; index < count; index += 1) {
    callback()
  }
}

const profileScenarios: Record<string, () => () => void> = {
  'create-patch': () => createContextRuntimeCreatePatchImmerBenchmarks().createPatchBatch,
  'reconcile': () => createContextRuntimeReconcileBenchmarks().runtimeReconcileBatch,
  'reconcile-plain-object': () =>
    createContextRuntimeReconcilePlainObjectBenchmarks().runtimeReconcilePlainObjectBatch,
  'snapshot': () => createContextRuntimeSnapshotBenchmarks().runtimeSnapshotBatch,
}

const scenarioFunction = profileScenarios[scenario]?.()

if (scenarioFunction === undefined) {
  const validScenarios = Object.keys(profileScenarios).join('|')

  console.error(`Unknown scenario: ${scenario}. Expected one of: ${validScenarios}`)
  process.exit(1)
}

console.log(`Profiling ${scenario} (${batchCount * BATCH_SIZE} operations)`)

runBatch(scenarioFunction, batchCount)
