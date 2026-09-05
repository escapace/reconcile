import { defineConfig, mergeConfig } from 'vitest/config'
import packageJSON from './package.json' with { type: 'json' }
import constants from './scripts/constants.json' with { type: 'json' }
import configShared from './vitest.config.ts'

export default mergeConfig(
  configShared,
  defineConfig({
    define: {
      ...['neutral', 'browser', 'node']
        .map(
          (target) =>
            (
              Reflect.get(constants.builds, target) as
                { define?: Record<string, string> } | undefined
            )?.define,
        )
        .find((value) => value !== undefined),
      __ENVIRONMENT__: JSON.stringify('development'),
      __VERSION__: JSON.stringify(packageJSON.version),
      __VITEST_PROJECT__: JSON.stringify('neutral'),
    },
    test: {
      environment: 'node',
      include: ['{src,test}/**/+([a-zA-Z0-9-]).{test,spec}.?(c|m)[jt]s?(x)'],
      name: 'neutral',
      sequence: {
        hooks: 'list',
      },
    },
  }),
)
