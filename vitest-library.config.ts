import path from 'node:path'
import { configDefaults, defineConfig, mergeConfig } from 'vitest/config'
import type { ViteUserConfig } from 'vitest/config'
import configNeutral, { scriptSpecs } from './vitest.config.neutral.ts'

// Runs the complete suite with the public modules resolved to the built package instead of
// the sources, so the published bundle (including its renamed internal member names) is
// held to the same contract. Specifications that inspect private source state explicitly
// import the `.ts` source entry; their spies cannot instrument bundled private members.
const library = path.join(import.meta.dirname, 'lib/neutral/index.js')

export default mergeConfig(
  configNeutral,
  defineConfig({
    resolve: {
      alias: [
        {
          find: /^(?:\.\.\/)+(?:deserialize|index|produce|reconcile|required-max-bytes|serialize|snapshot)$/,
          replacement: library,
        },
      ],
    },
    test: {
      // Besides the script specs, these import the sources on purpose.
      exclude: [
        ...configDefaults.exclude,
        ...scriptSpecs,
        'src/__tests__/classification-work.spec.ts',
        'src/__tests__/produce-publication-boundary.spec.ts',
      ],
      name: 'library',
    },
  }),
) as ViteUserConfig
