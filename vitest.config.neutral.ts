import { defineConfig, mergeConfig } from 'vitest/config'
import type { ViteUserConfig } from 'vitest/config'
import { version } from './package.json' with { type: 'json' }
import { builds } from './scripts/constants.json' with { type: 'json' }
import configShared from './vitest.config.ts'

/** Specs that run no library code in their own process: they test scripts or drive a child
 * process, so the poisoned and library projects would repeat the neutral run. */
export const scriptSpecs = [
  'src/__tests__/ab-time.spec.ts',
  'src/__tests__/bench-workloads.spec.ts',
  'src/__tests__/bounded-check.spec.ts',
  'src/__tests__/profile-attribution.spec.ts',
  'src/__tests__/profile-counts.spec.ts',
  'src/__tests__/standard-prototypes.spec.ts',
]

const config = mergeConfig(
  configShared,
  defineConfig({
    define: {
      ...builds.neutral.define,
      __ENVIRONMENT__: JSON.stringify('development'),
      __VERSION__: JSON.stringify(version),
      __VITEST_PROJECT__: JSON.stringify('neutral'),
    },
    test: {
      environment: 'node',
      include: ['src/**/+([a-zA-Z0-9-]).{test,spec}.?(c|m)[jt]s?(x)'],
      name: 'neutral',
      sequence: {
        hooks: 'list',
      },
      // The longest seeded batches and child-process drivers take up to a minute alone.
      testTimeout: 120_000,
    },
  }),
) as ViteUserConfig

// Drop the shared workspace after merging: as a project, this file otherwise lists the projects
// again, and the poisoned project builds on it.
const { projects: _projects, ...test } = config.test ?? {}
export default defineConfig({ ...config, test })
