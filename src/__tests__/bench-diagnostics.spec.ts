import { it } from 'vitest'
import { createDiagnostic, diagnosticNames } from '../../scripts/bench/diagnostics'
import { deserialize, produce, reconcile, requiredMaxBytes, serialize, snapshot } from '../index'

it.each(diagnosticNames)('validates repeated diagnostic operations: %s', (name) => {
  const scenario = createDiagnostic(
    name,
    { deserialize, produce, reconcile, requiredMaxBytes, serialize, snapshot },
    8,
  )
  // Twelve operations cover the six rotating serialization fixtures twice.
  for (let operation = 0; operation < 12; operation += 1) {
    scenario.run()
    scenario.validate()
  }
})
