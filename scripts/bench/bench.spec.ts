import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import path from 'node:path'
import { afterAll, describe, expect, it, vi } from 'vitest'

const state = mkdtempSync(path.join(tmpdir(), 'reconcile-bench-spec-'))
process.env.RECONCILE_STATE = state
const { main } = await import('../framework/command')
const { bench } = await import('./bench')
const { frozenHash, sourceHash } = await import('./provenance')
const { resolveControl } = await import('./experiments')

/** An experiment without rounds, as `pnpm bench control` leaves it: a control tree, pinned. */
const experiment = path.join(state, 'experiments', '20260101-000000-abc1234')
const control = path.join(experiment, 'tree')
mkdirSync(path.join(experiment, 'rounds'), { recursive: true })
mkdirSync(path.join(control, 'src'), { recursive: true })
writeFileSync(path.join(control, 'src', 'index.ts'), 'export {}\n')
writeFileSync(
  path.join(experiment, 'experiment.json'),
  JSON.stringify({
    commit: 'abc1234',
    created: 'then',
    frozenWorkloadSha256: frozenHash(control),
    sourceSha256: sourceHash(control),
    worktree: false,
  }),
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
    [['ab', 'default'], 'ab needs --control <control>'],
    [['ab', '--control', 'nowhere'], 'no experiment or source tree "nowhere"'],
    [['ab', '--control', '.', '--pairs', '3'], '--pairs takes an even count'],
    [['ab', '--control', 'latest', '--pairs', '3'], '--pairs takes an even count'],
    [['ab', '--control', 'latest', '--seconds', '0'], '--seconds takes a positive number'],
    [['ab', '--scenario', 'reconcile'], 'pnpm bench <command> <scenario...>'],
    [['counts', 'reconcile', '--baseline', 'x'], '--baseline no longer exists: use --control'],
    [['size', '--compare', 'x'], '--compare no longer exists: use --control'],
    [['control', '--build'], '`pnpm bench size` builds both trees itself'],
    [
      ['ab', 'reconcile', '--control', 'latest', '--decide', '--batches', '20'],
      'a deciding round sizes',
    ],
    [
      ['ab', 'reconcile', '--control', 'latest', '--decide', '--warmup', '0'],
      'a deciding round sizes',
    ],
    [['counts', 'constructor'], 'unknown scenarios: constructor'],
    [['profile', 'toString'], 'unknown scenarios: toString'],
    [['counts', 'reconcile', '--warmup='], '--warmup takes an integer'],
    [['counts', 'reconcile', '--batches', '1e1'], '--batches takes an integer'],
    [['ab', '--control', 'latest', '--seconds', '0x1'], '--seconds takes a positive number'],
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

  it('refuses an experiment whose control changed after it was frozen', async () => {
    writeFileSync(path.join(control, 'src', 'edit.ts'), 'export {}\n')
    try {
      const result = await cli('ab', 'reconcile', '--control', 'latest')
      expect(result.code).toBe(3)
      expect(result.stderr).toContain('changed after it was frozen (src/)')
    } finally {
      rmSync(path.join(control, 'src', 'edit.ts'))
    }
  })

  it('takes the control tree of an experiment as the experiment, keeping its rounds', () => {
    expect(resolveControl(control)).toEqual({
      rounds: path.join(experiment, 'rounds'),
      tree: control,
    })
    expect(resolveControl('latest')).toEqual(resolveControl(control))
  })

  it('refuses to compare trees whose frozen workloads differ', async () => {
    // The spec's control has no perf/ at all.
    const result = await cli('ab', 'reconcile', '--control', 'latest')
    expect(result.code).toBe(3)
    expect(result.stderr).toContain('the frozen workloads in perf/')
  })

  it('skips an experiment whose record cannot be read', () => {
    const broken = path.join(state, 'experiments', '20260102-000000-broken')
    mkdirSync(broken, { recursive: true })
    writeFileSync(path.join(broken, 'experiment.json'), '{"comm')
    try {
      expect(resolveControl('latest').tree).toBe(control)
    } finally {
      rmSync(broken, { force: true, recursive: true })
    }
  })

  it('reports an experiment without rounds', async () => {
    const result = await cli('report')
    expect(result.code).toBe(0)
    expect(result.stdout).toContain('No A/B round of a change yet')
  })
})
