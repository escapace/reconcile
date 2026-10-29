import { checkSerializationCollectionRuntime } from './bridges/serialization-collection'
import { checkSerializationRuntime } from './bridges/serialization'
import assert from 'node:assert/strict'
import { checkNativeValueRuntime } from './bridges/native-value'
import { checkOwnedNativeChildRuntime } from './bridges/owned-native-child'
import { checkCapturedRuntime } from './bridges/captured'
import { checkSpecGate } from './bridges/spec'
import { checkSpecPhasesGate } from './bridges/spec-phases'
import { checkSpecEnumerationGate } from './bridges/spec-enumeration'
import { startOracle } from './oracle'
import { checkPropertyOrderRuntime } from './bridges/property-order'
import { checkAtomsRuntime } from './bridges/atoms'
import { checkIngressRuntime } from './bridges/ingress'
import { checkRecognitionPlainRuntime } from './bridges/recognition-plain'
import { checkSettledChildrenRuntime } from './bridges/settled-children'
import { checkSpecialValuesRuntime } from './bridges/special-values'
import { checkWriteFreeReadbackRuntime } from './bridges/write-free-readback'
import { checkCollectionWritesRuntime } from './bridges/collection-writes'
import { checkCopyPrototypeRuntime } from './bridges/copy-prototype'
import { checkDraftSurfaceRuntime } from './bridges/draft-surface'
import { checkDraftClassRuntime } from './bridges/draft-class'
import { checkDraftIterationRuntime } from './bridges/draft-iteration'
import { checkDraftMembersRuntime } from './bridges/draft-members'
import { checkDraftSetMethodsRuntime } from './bridges/draft-set-methods'
import { checkKeyOrderRuntime } from './bridges/key-order'
import { checkPropertyConstructRuntime } from './bridges/property-construct'
import { checkPropertyThroughSetterRuntime } from './bridges/property-through-setter'
import { checkPropertyPlacementRuntime } from './bridges/property-placement'
import { checkPropertyWriteRuntime } from './bridges/property-write'
import { checkSeededRequirementsRuntime } from './bridges/seeded-requirements'
import { checkDeferredOrderRuntime } from './bridges/deferred-order'
import { checkFactRenamingRuntime } from './bridges/fact-renaming'
import { checkCompactImmutableRuntime } from './bridges/compact-immutable'

const oracle = await startOracle()
let overflowChecked = false
try {
  // Rejected requests must not corrupt the next response or silently become passes.
  await assert.rejects(oracle.run('Unknown'), /Unknown oracle family/)
  await assert.rejects(oracle.run('DeferredOrder', { input: '{}' }), /expected JSON array/)
  await assert.rejects(oracle.run('Contract', { maxBuffer: 0 }), /Invalid oracle output limit/)
  const pending = oracle.run('Atoms')
  await assert.rejects(oracle.run('Atoms'), /open, idle session/)
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
  await checkSpecialValuesRuntime(oracle.run)
  await checkWriteFreeReadbackRuntime(oracle.run)
  await checkCollectionWritesRuntime(oracle.run)
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
  await checkSpecPhasesGate(oracle.run)
  await checkSpecEnumerationGate(oracle.run)
  // Bound a response before a whole oversized line can accumulate. Shutdown must
  // preserve the original diagnostic rather than mask it with the killed exit code.
  await assert.rejects(oracle.run('Atoms', { maxBuffer: 1 }), /output exceeds 1 bytes/)
  overflowChecked = true
} finally {
  if (overflowChecked) await assert.rejects(oracle.close(), /output exceeds 1 bytes/)
  else await oracle.close()
}
