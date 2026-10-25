import { checkSerializationCollectionRuntime } from './check-serialization-collection-runtime'
import { checkSerializationRuntime } from './check-serialization-lean'
import assert from 'node:assert/strict'
import { checkNativeValueRuntime } from './check-native-value-runtime'
import { checkOwnedNativeChildRuntime } from './check-owned-native-child-runtime'
import { checkCapturedRuntime } from './lean-captured-bridge'
import { checkSpecGate } from './lean-spec-bridge'
import { startOracle } from './lean-oracle'
import { checkPropertyOrderRuntime } from './check-property-order-runtime'
import { checkAtomsRuntime } from './check-atoms-runtime'
import { checkIngressRuntime } from './check-ingress-runtime'
import { checkRecognitionPlainRuntime } from './check-recognition-plain-runtime'
import { checkSettledChildrenRuntime } from './check-settled-children-runtime'
import { checkWriteFreeReadbackRuntime } from './check-write-free-readback-runtime'
import { checkCopyPrototypeRuntime } from './check-copy-prototype-runtime'
import { checkDraftSurfaceRuntime } from './check-draft-surface-runtime'
import { checkDraftClassRuntime } from './check-draft-class-runtime'
import { checkDraftIterationRuntime } from './check-draft-iteration-runtime'
import { checkDraftMembersRuntime } from './check-draft-members-runtime'
import { checkDraftSetMethodsRuntime } from './check-draft-set-methods-runtime'
import { checkKeyOrderRuntime } from './check-key-order-runtime'
import { checkPropertyConstructRuntime } from './check-property-construct-runtime'
import { checkPropertyThroughSetterRuntime } from './check-property-through-setter-runtime'
import { checkPropertyPlacementRuntime } from './check-property-placement-runtime'
import { checkPropertyWriteRuntime } from './check-property-write-runtime'
import { checkSeededRequirementsRuntime } from './check-seeded-requirements-runtime'
import { checkDeferredOrderRuntime } from './check-deferred-order-runtime'
import { checkFactRenamingRuntime } from './check-fact-renaming-runtime'
import { checkCompactImmutableRuntime } from './check-compact-immutable-runtime'

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
  await checkPropertyOrderRuntime(oracle.run)
  await checkPropertyWriteRuntime(oracle.run)
  await checkPropertyPlacementRuntime(oracle.run)
  await checkPropertyConstructRuntime(oracle.run)
  await checkPropertyThroughSetterRuntime(oracle.run)
  await checkKeyOrderRuntime(oracle.run)
  await checkAtomsRuntime(oracle.run)
  await checkRecognitionPlainRuntime(oracle.run)
  await checkIngressRuntime(oracle.run)
  await checkSettledChildrenRuntime(oracle.run)
  await checkWriteFreeReadbackRuntime(oracle.run)
  await checkDraftSurfaceRuntime(oracle.run)
  await checkDraftClassRuntime(oracle.run)
  await checkDraftIterationRuntime(oracle.run)
  await checkDraftMembersRuntime(oracle.run)
  await checkDraftSetMethodsRuntime(oracle.run)
  await checkCopyPrototypeRuntime(oracle.run)
  await checkSeededRequirementsRuntime(oracle.run)
  await checkDeferredOrderRuntime(oracle.run)
  await checkFactRenamingRuntime(oracle.run)
  await checkCompactImmutableRuntime(oracle.run)
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
