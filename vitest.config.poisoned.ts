import { configDefaults, defineConfig, mergeConfig } from 'vitest/config'
import type { ViteUserConfig } from 'vitest/config'
import configNeutral, { scriptSpecs } from './vitest.config.neutral.ts'

// The complete suite with a proxy behind Array.prototype that fails a test in which library code
// reads or writes through it; see the setup file.
export default mergeConfig(
  configNeutral,
  defineConfig({
    test: {
      exclude: [...configDefaults.exclude, ...scriptSpecs],
      name: 'poisoned',
      setupFiles: ['src/__tests__/fixtures/poisoned-prototypes.ts'],
      // Every array read of a hole or past the end passes through the proxy and, when the suite
      // replays long native edit sequences, is attributed to its caller.
      testTimeout: 180_000,
    },
  }),
) as ViteUserConfig
