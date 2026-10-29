import { existsSync } from 'node:fs'
import { defineConfig, mergeConfig } from 'vitest/config'
import type { ViteUserConfig } from 'vitest/config'
import configShared from './vitest.config.ts'

/** Specs that run no library code in their own process: the tooling's specs beside it in
 * `scripts/`, and this one, which drives a child process. The poisoned and library projects would
 * repeat the neutral run of them. */
export const scriptSpecs = ['scripts/**', 'src/__tests__/standard-prototypes.spec.ts']
// A renamed spec would otherwise run in every project without a word.
for (const spec of scriptSpecs)
  if (!spec.includes('*') && !existsSync(spec)) throw new Error(`${spec} does not exist`)

const config = mergeConfig(
  configShared,
  defineConfig({
    test: {
      include: ['scripts/**/*.spec.ts', 'src/**/*.spec.ts'],
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
