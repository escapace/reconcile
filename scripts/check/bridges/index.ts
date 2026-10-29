import type { Oracle } from '../oracle'
import type { Selection } from './selection'

/** A narrowing option that only some bridges with batches take. */
export type Flag = '--dump' | '--features' | '--seeds'

/** One runtime-to-Lean bridge: its family name, as `pnpm check lean` takes it, the batches it
 * runs, if it has several, the narrowing options it takes besides `--batch`, and a loader, so
 * that naming the bridges loads none of them. */
export interface Bridge {
  readonly family: string
  readonly batches?: readonly string[]
  readonly takes?: readonly Flag[]
  readonly load: () => Promise<(oracle: Oracle, selection: Selection) => Promise<void>>
}

/** Every bridge, in the order the gate runs them. */
export const BRIDGES: readonly Bridge[] = [
  { family: 'captured', load: async () => (await import('./captured')).checkCapturedRuntime },
  {
    family: 'property-order',
    load: async () => (await import('./property-order')).checkPropertyOrderRuntime,
  },
  {
    family: 'property-write',
    load: async () => (await import('./property-write')).checkPropertyWriteRuntime,
  },
  {
    family: 'property-placement',
    load: async () => (await import('./property-placement')).checkPropertyPlacementRuntime,
  },
  {
    family: 'property-construct',
    load: async () => (await import('./property-construct')).checkPropertyConstructRuntime,
  },
  {
    family: 'property-through-setter',
    load: async () => (await import('./property-through-setter')).checkPropertyThroughSetterRuntime,
  },
  { family: 'key-order', load: async () => (await import('./key-order')).checkKeyOrderRuntime },
  { family: 'atoms', load: async () => (await import('./atoms')).checkAtomsRuntime },
  {
    family: 'recognition-plain',
    load: async () => (await import('./recognition-plain')).checkRecognitionPlainRuntime,
  },
  { family: 'ingress', load: async () => (await import('./ingress')).checkIngressRuntime },
  {
    family: 'settled-children',
    load: async () => (await import('./settled-children')).checkSettledChildrenRuntime,
  },
  {
    family: 'special-values',
    load: async () => (await import('./special-values')).checkSpecialValuesRuntime,
  },
  {
    family: 'write-free-readback',
    load: async () => (await import('./write-free-readback')).checkWriteFreeReadbackRuntime,
  },
  {
    family: 'collection-writes',
    load: async () => (await import('./collection-writes')).checkCollectionWritesRuntime,
  },
  {
    family: 'draft-surface',
    load: async () => (await import('./draft-surface')).checkDraftSurfaceRuntime,
  },
  {
    family: 'draft-class',
    load: async () => (await import('./draft-class')).checkDraftClassRuntime,
  },
  {
    family: 'draft-iteration',
    load: async () => (await import('./draft-iteration')).checkDraftIterationRuntime,
  },
  {
    family: 'draft-members',
    load: async () => (await import('./draft-members')).checkDraftMembersRuntime,
  },
  {
    family: 'draft-set-methods',
    load: async () => (await import('./draft-set-methods')).checkDraftSetMethodsRuntime,
  },
  {
    family: 'copy-prototype',
    load: async () => (await import('./copy-prototype')).checkCopyPrototypeRuntime,
  },
  {
    family: 'seeded-requirements',
    load: async () => (await import('./seeded-requirements')).checkSeededRequirementsRuntime,
  },
  {
    family: 'deferred-order',
    load: async () => (await import('./deferred-order')).checkDeferredOrderRuntime,
  },
  {
    family: 'fact-renaming',
    load: async () => (await import('./fact-renaming')).checkFactRenamingRuntime,
  },
  {
    family: 'compact-immutable',
    load: async () => (await import('./compact-immutable')).checkCompactImmutableRuntime,
  },
  {
    family: 'native-value',
    load: async () => (await import('./native-value')).checkNativeValueRuntime,
  },
  {
    family: 'owned-native-child',
    load: async () => (await import('./owned-native-child')).checkOwnedNativeChildRuntime,
  },
  {
    family: 'serialization',
    load: async () => (await import('./serialization')).checkSerializationRuntime,
  },
  {
    family: 'serialization-collection',
    load: async () =>
      (await import('./serialization-collection')).checkSerializationCollectionRuntime,
  },
  {
    batches: [
      'reconcile',
      'reconcile-hazards',
      'reconcile-binary',
      'reconcile-next-accessors',
      'produce',
      'produce-binary',
      'snapshot',
      'snapshot-binary',
      'roundtrip-binary',
    ],
    family: 'spec',
    takes: ['--dump', '--features', '--seeds'],
    load: async () => (await import('./spec')).checkSpecGate,
  },
  {
    batches: ['plain', 'hazards', 'binary'],
    family: 'spec-phases',
    takes: ['--dump', '--seeds'],
    load: async () => (await import('./spec-phases')).checkSpecPhasesGate,
  },
  {
    batches: [
      'arrays',
      'attributes',
      'binary',
      'classes',
      'collections',
      'dates',
      'holders',
      'structure',
      'produce-attributes',
      'produce-structure',
      'snapshot',
    ],
    family: 'spec-enumeration',
    load: async () => (await import('./spec-enumeration')).checkSpecEnumerationGate,
  },
]
