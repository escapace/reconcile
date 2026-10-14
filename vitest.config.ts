import { configDefaults, defineConfig } from 'vitest/config'

export default defineConfig({
  test: {
    coverage: {
      exclude: [
        '**/example*.ts',
        'src/test-support/**',
        ...(configDefaults.coverage.exclude ?? []),
      ],
      include: ['src/**'],
      provider: 'v8',
    },
    include: [],
    // Large graph cases pass alone but exceed their deadlines under worker contention.
    maxWorkers: 2,
    passWithNoTests: true,
    projects: ['vitest.config.*.ts'],
    reporters: ['minimal'],
  },
})
