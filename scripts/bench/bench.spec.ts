import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import path from 'node:path'
import { afterAll, describe, expect, it, vi } from 'vitest'

const state = mkdtempSync(path.join(tmpdir(), 'reconcile-bench-spec-'))
process.env.RECONCILE_STATE = state
const { main } = await import('../framework/command')
const { bench } = await import('./bench')

/** An experiment without rounds, as `pnpm bench control` leaves it. */
const experiment = path.join(state, 'experiments', '20260101-000000-abc1234')
mkdirSync(path.join(experiment, 'rounds'), { recursive: true })
writeFileSync(
  path.join(experiment, 'experiment.json'),
  JSON.stringify({ commit: 'abc1234', created: 'then', worktree: false }),
)

/** Runs `pnpm bench` with `argv` and returns its exit code with what it wrote. */
async function cli(...argv: string[]): Promise<{ code: number; stderr: string; stdout: string }> {
  let stdout = ''
  let stderr = ''
  vi.spyOn(process.stdout, 'write').mockImplementation((text) => {
    stdout += String(text)
    return true
  })
  vi.spyOn(process.stderr, 'write').mockImplementation((text) => {
    stderr += String(text)
    return true
  })
  vi.spyOn(console, 'log').mockImplementation((text: unknown) => {
    stdout += `${String(text)}\n`
  })
  try {
    return { code: await main([bench], ['bench', ...argv]), stderr, stdout }
  } finally {
    vi.restoreAllMocks()
  }
}

afterAll(() => {
  rmSync(state, { force: true, recursive: true })
})

describe('pnpm bench', () => {
  it.each([
    [['profile'], 'profile takes one scenario'],
    [['profile', 'default'], 'profile takes one scenario'],
    [['profile', 'reconcile', '--mode', 'counts'], 'pnpm bench counts <scenario>'],
    [['profile', 'reconcile', '--mode', 'wall'], '--mode takes cpu, heap or deopt'],
    [['profile', 'nothing'], 'unknown scenarios: nothing'],
    [['counts'], 'counts takes at least one scenario'],
    [['counts', 'reconcile', '--batches', '0'], '--batches takes an integer of at least 1'],
    [['ab', 'default'], 'ab needs --control <experiment>'],
    [['ab', '--control', 'nowhere'], 'no experiment "nowhere"'],
    [['ab', '--control', 'latest', '--pairs', '3'], '--pairs takes an even count'],
    [['ab', '--control', 'latest', '--seconds', '0'], '--seconds takes a positive number'],
    [['ab', '--scenario', 'reconcile'], 'pnpm bench ab <scenario...>'],
    [['size', '--modules', 'reconcile+nothing'], '--modules takes exports'],
    [['control', 'HEAD', 'HEAD~1'], 'control takes one revision, or --worktree'],
    [['control', 'HEAD', '--worktree'], 'control takes one revision, or --worktree'],
    [['control', 'no-such-revision'], 'no revision "no-such-revision"'],
    [['report', 'a', 'b'], 'report takes one experiment'],
  ])('refuses %j before measuring anything', async (argv, message) => {
    const result = await cli(...argv)
    expect(result.code).toBe(2)
    expect(result.stderr).toContain(message)
  })

  it('reports an experiment without rounds', async () => {
    const result = await cli('report')
    expect(result.code).toBe(0)
    expect(result.stdout).toContain('No A/B round yet')
  })
})
