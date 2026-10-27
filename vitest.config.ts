import { defineConfig } from 'vitest/config'

export default defineConfig({
  test: {
    coverage: { include: ['src/**'] },
    // Large graph cases pass alone but exceed their deadlines under worker contention.
    maxWorkers: 2,
    passWithNoTests: true,
    projects: ['vitest.config.*.ts'],
    reporters: ['minimal'],
  },
})
