import { DATE_KIND } from '../types/date'
import { ARRAY_BUFFER_KIND } from '../types/array-buffer'
import { it } from 'vitest'
import { createDiagnostic, diagnosticNames } from '../../scripts/profile-scenarios'
import { deserialize, produce, reconcile, requiredMaxBytes, serialize, snapshot } from '../index'
import { builtinTypes } from '../types/builtins'

it.each(diagnosticNames)('validates repeated diagnostic operations: %s', (name) => {
  const scenario = createDiagnostic(
    name,
    {
      copyDate: builtinTypes.specials[DATE_KIND]!.copy,
      deserialize,
      produce,
      reconcile,
      requiredMaxBytes,
      sameBuffer: builtinTypes.specials[ARRAY_BUFFER_KIND]!.equivalent,
      serialize,
      snapshot,
    },
    8,
  )
  // Twelve operations cover the six rotating serialization fixtures twice.
  for (let operation = 0; operation < 12; operation += 1) {
    scenario.run()
    scenario.validate()
  }
})
