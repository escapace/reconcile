import { defineConfig, mergeConfig } from 'vitest/config'
import type { ViteUserConfig } from 'vitest/config'
import { version } from './package.json' with { type: 'json' }
import { builds } from './scripts/constants.json' with { type: 'json' }
import configShared from './vitest.config.ts'

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
    },
  }),
) as ViteUserConfig

// Drop the shared workspace after merging: as a project, this file otherwise lists the projects
// again, and the poisoned project builds on it.
const { projects: _projects, ...test } = config.test ?? {}
export default defineConfig({ ...config, test })
