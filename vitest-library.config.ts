import path from 'node:path'
import { defineConfig, mergeConfig } from 'vitest/config'
import configNeutral from './vitest.config.neutral.ts'

// Runs the complete suite with the public modules resolved to the built package instead of
// the sources, so the published bundle (including its renamed internal member names) is
// held to the same contract. Specifications that also import internal modules exercise
// those internals from the sources, as in `pnpm test`.
const library = path.join(import.meta.dirname, 'lib/neutral/index.js')

export default mergeConfig(
  configNeutral,
  defineConfig({
    resolve: {
      alias: [{ find: /^\.\.\/(?:index|produce|reconcile|snapshot)$/, replacement: library }],
    },
    test: { coverage: { enabled: false }, name: 'library' },
  }),
)
