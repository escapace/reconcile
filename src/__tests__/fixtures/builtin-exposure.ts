import { ExposurePalette, exposureMode } from '../../adapters/vue'
import { builtinTypes } from '../../types/builtins'

const exposureOf = (value: object) => builtinTypes.exposures[builtinTypes.recognize(value)!]

/** An exposure palette bound to the built-in registry. */
export class BuiltinExposurePalette extends ExposurePalette {
  constructor() {
    super(exposureOf)
  }
}

/** The exposure mode of `value` under the built-in registry. */
export const builtinExposureMode = (value: object): number | undefined =>
  exposureMode(value, exposureOf)
