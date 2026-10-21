import { execFileSync } from 'node:child_process'
import path from 'node:path'
import { expect, it } from 'vitest'

it('classifies pnpm bench ab rounds and sizes their batches', () => {
  const root = path.resolve(import.meta.dirname, '../..')
  expect(
    execFileSync('python3', ['scripts/test-ab-time.py'], { cwd: root, encoding: 'utf8' }),
  ).toContain('ab-time decision logic verified')
})
