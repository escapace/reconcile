import path from 'node:path'
import { defineConfig, mergeConfig } from 'vitest/config'
import type { ViteUserConfig } from 'vitest/config'
import configNeutral from './vitest.config.neutral.ts'

// Runs the complete suite with the public modules resolved to the built package instead of
// the sources, so the published bundle (including its renamed internal member names) is
// held to the same contract. Specifications that inspect private source state explicitly
// import the `.ts` source entry; their spies cannot instrument bundled private members.
const library = path.join(import.meta.dirname, 'lib/neutral/index.js')

const config = mergeConfig(
  configNeutral,
  defineConfig({
    resolve: {
      alias: [{ find: /^\.\.\/(?:index|produce|reconcile|snapshot)$/, replacement: library }],
    },
    test: { coverage: { enabled: false }, name: 'library' },
  }),
) as ViteUserConfig

// Clear the shared workspace after merging: child projects otherwise bypass these aliases.
export default defineConfig({ ...config, test: { ...config.test, projects: undefined } })
