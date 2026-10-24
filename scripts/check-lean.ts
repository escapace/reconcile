import { checkSerializationCollectionRuntime } from './check-serialization-collection-runtime'
import { checkSerializationRuntime } from './check-serialization-lean'
import assert from 'node:assert/strict'
import { checkNativeValueRuntime } from './check-native-value-runtime'
import { checkOwnedNativeChildRuntime } from './check-owned-native-child-runtime'
import { checkCapturedRuntime } from './lean-captured-bridge'
import { checkPolicyRuntime } from './lean-policy-bridge'
import { checkPrunedRuntime } from './lean-pruned-bridge'
import { checkSpecGate } from './lean-spec-bridge'
import { startOracle } from './lean-oracle'

const oracle = await startOracle()
let overflowChecked = false
try {
  // Rejected requests must not corrupt the next response or silently become passes.
  await assert.rejects(oracle.run('Unknown'), /Unknown oracle family/)
  await assert.rejects(oracle.run('DeferredOrder', [], { input: '{}' }), /expected JSON array/)
  await assert.rejects(oracle.run('Contract', [], { maxBuffer: 0 }), /Invalid oracle output limit/)
  const pending = oracle.run('Contract')
  await assert.rejects(oracle.run('Contract'), /open, idle session/)
  await pending
  await checkCapturedRuntime(oracle.run)
  await checkPolicyRuntime(oracle.run)
  await checkPrunedRuntime(oracle.run)
  await checkNativeValueRuntime(oracle.run)
  await checkOwnedNativeChildRuntime(oracle.run)
  await checkSerializationRuntime(oracle.run)
  await checkSerializationCollectionRuntime(oracle.run)
  await checkSpecGate(oracle.run)
  // Bound a response before a whole oversized line can accumulate. Shutdown must
  // preserve the original diagnostic rather than mask it with the killed exit code.
  await assert.rejects(oracle.run('Contract', [], { maxBuffer: 1 }), /output exceeds 1 bytes/)
  overflowChecked = true
} finally {
  if (overflowChecked) await assert.rejects(oracle.close(), /output exceeds 1 bytes/)
  else await oracle.close()
}
