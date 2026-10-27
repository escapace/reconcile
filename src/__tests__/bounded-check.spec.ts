import { execFileSync } from 'node:child_process'
import path from 'node:path'
import { expect, it } from 'vitest'

it('stops a timed-out process tree and rejects an invalid budget', () => {
  const root = path.resolve(import.meta.dirname, '../..')
  expect(
    execFileSync('python3', ['scripts/test-bounded-check.py'], { cwd: root, encoding: 'utf8' }),
  ).toContain('invalid budget rejected')
})
