import { spawn, spawnSync } from 'node:child_process'
import { existsSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import path from 'node:path'
import { setTimeout as sleep } from 'node:timers/promises'
import { afterAll, describe, expect, it } from 'vitest'

const state = mkdtempSync(path.join(tmpdir(), 'reconcile-round-spec-'))
process.env.RECONCILE_STATE = state
const { runRound } = await import('./round')

const shell = (name: string, script: string) => ({ command: ['sh', '-c', script], name })

/** Whether a process still runs: a killed one may linger as a zombie until it is reaped. */
const alive = (pid: number): boolean => {
  const stat = spawnSync('ps', ['-o', 'stat=', '-p', String(pid)], {
    encoding: 'utf8',
  }).stdout.trim()
  return stat !== '' && !stat.startsWith('Z')
}

afterAll(() => {
  rmSync(state, { force: true, recursive: true })
})

const receiptOf = (file: string): Record<string, unknown> =>
  JSON.parse(readFileSync(file, 'utf8')) as Record<string, unknown>

/** Runs a round in a CLI-like driver that handles interrupts, and returns how it ended. */
async function driven(
  name: string,
  step: string,
  signals: readonly NodeJS.Signals[],
): Promise<{ directory: string; pid: number; seconds: number; signal: NodeJS.Signals | null }> {
  const directory = mkdtempSync(path.join(state, `${name}-`))
  const pidFile = path.join(directory, 'pid')
  // Outside the repository only the .mts extension makes the driver an ES module.
  const driver = path.join(directory, 'driver.mts')
  const framework = (file: string): string => JSON.stringify(path.join(import.meta.dirname, file))
  writeFileSync(
    driver,
    `import { finish, handleInterrupts } from ${framework('interrupt.ts')}
import { runRound } from ${framework('round.ts')}
handleInterrupts()
const result = await runRound({ directory: ${JSON.stringify(directory)}, name: 'cancel', steps: [
{ command: ['sh', '-c', ${JSON.stringify(`echo $$ > ${pidFile}; ${step}`)}], name: 'sleeper' }] })
finish(result.exitCode)\n`,
  )
  const child = spawn(process.execPath, ['--import', 'tsx', driver], {
    env: { ...process.env, RECONCILE_STATE: state },
    stdio: 'ignore',
  })
  const closed = new Promise<NodeJS.Signals | null>((resolve) =>
    child.once('close', (_, signal) => resolve(signal)),
  )
  const started = (): boolean => existsSync(pidFile) && readFileSync(pidFile, 'utf8') !== ''
  while (child.exitCode === null && !started()) await sleep(50)
  const interrupted = performance.now()
  for (const signal of signals) {
    child.kill(signal)
    await sleep(100)
  }
  const signal = await closed
  const seconds = (performance.now() - interrupted) / 1000
  return { directory, pid: Number(readFileSync(pidFile, 'utf8')), seconds, signal }
}

describe('runRound', () => {
  it('runs every step and writes a receipt when they pass', async () => {
    const result = await runRound({
      name: 'pass',
      steps: [shell('first', 'echo one'), shell('second', 'echo two')],
    })
    expect(result.status).toBe('passed')
    expect(result.exitCode).toBe(0)
    expect(result.steps.map((step) => step.name)).toEqual(['first', 'second'])
    expect(readFileSync(result.steps[1].log, 'utf8')).toBe('two\n')
    expect(receiptOf(result.receipt)).toMatchObject({ budgetSeconds: 295, status: 'passed' })
  })

  it("stops at the first step that fails, exits 1 and keeps the step's code in the receipt", async () => {
    const result = await runRound({
      name: 'fail',
      steps: [shell('failing', 'exit 3'), shell('never', 'echo never')],
    })
    expect(result.status).toBe('failed')
    expect(result.exitCode).toBe(1)
    expect(result.steps).toHaveLength(1)
    expect(result.steps[0].exitCode).toBe(3)
  })

  it("adds a step's environment and its deadline", async () => {
    const result = await runRound({
      name: 'environment',
      steps: [
        {
          ...shell('resolved', 'echo "$VALUE ${RECONCILE_DEADLINE:+deadline}"'),
          env: { VALUE: 'set' },
        },
      ],
    })
    expect(readFileSync(result.steps[0].log, 'utf8')).toBe('set deadline\n')
  })

  it('exits 3, judging nothing, when a command cannot be started', async () => {
    const result = await runRound({
      name: 'missing',
      steps: [{ command: ['reconcile-no-such-command'], name: 'missing' }, shell('never', 'true')],
    })
    expect(result.status).toBe('blocked')
    expect(result.exitCode).toBe(3)
    expect(result.steps).toHaveLength(1)
    expect(readFileSync(result.steps[0].log, 'utf8')).toContain(
      'cannot run reconcile-no-such-command',
    )
  })

  it('stops a step that outlives the budget, with every process it started', async () => {
    const directory = mkdtempSync(path.join(state, 'timeout-'))
    const pidFile = path.join(directory, 'pid')
    const result = await runRound({
      budgetSeconds: 3,
      directory,
      name: 'timeout',
      steps: [
        shell(
          'stubborn',
          `trap "" TERM; (trap "" TERM; sleep 60) & echo $! > ${pidFile}; sleep 60`,
        ),
      ],
    })
    expect(result.status).toBe('timed_out')
    expect(result.exitCode).toBe(124)
    expect(alive(Number(readFileSync(pidFile, 'utf8')))).toBe(false)
  })

  it('stops what a passing step left running', async () => {
    const directory = mkdtempSync(path.join(state, 'leftover-'))
    const pidFile = path.join(directory, 'pid')
    const result = await runRound({
      directory,
      name: 'leftover',
      steps: [shell('detached', `(sleep 60) > /dev/null 2>&1 & echo $! > ${pidFile}`)],
    })
    expect(result.status).toBe('passed')
    expect(alive(Number(readFileSync(pidFile, 'utf8')))).toBe(false)
  })

  it.runIf(process.platform === 'linux')(
    'stops a descendant that left the process group but holds the output open',
    async () => {
      const directory = mkdtempSync(path.join(state, 'escaped-'))
      const pidFile = path.join(directory, 'pid')
      const started = performance.now()
      const result = await runRound({
        directory,
        name: 'escaped',
        steps: [shell('escaped', `setsid sh -c 'echo $$ > ${pidFile}; exec sleep 60' & sleep 0.5`)],
      })
      expect(result.status).toBe('passed')
      expect(performance.now() - started).toBeLessThan(10_000)
      expect(alive(Number(readFileSync(pidFile, 'utf8')))).toBe(false)
      expect(readFileSync(result.steps[0].log, 'utf8')).toContain('left the step')
    },
  )

  it('never overwrites a receipt', async () => {
    const directory = mkdtempSync(path.join(state, 'twice-'))
    await runRound({ directory, name: 'once', steps: [shell('step', 'true')] })
    await expect(
      runRound({ directory, name: 'twice', steps: [shell('step', 'true')] }),
    ).rejects.toThrow(/EEXIST/)
  })

  it('rejects a budget beyond 300 seconds', async () => {
    await expect(runRound({ budgetSeconds: 301, name: 'long', steps: [] })).rejects.toThrow(
      RangeError,
    )
  })

  it('records an interrupted round as cancelled, stops its step and ends by the signal', async () => {
    const { directory, pid, signal } = await driven('cancel', 'sleep 60', ['SIGINT'])
    expect(signal).toBe('SIGINT')
    expect(receiptOf(path.join(directory, 'receipt.json'))).toMatchObject({ status: 'cancelled' })
    expect(alive(pid)).toBe(false)
  })

  it('stops a step that ignores SIGTERM at once on a second interrupt', async () => {
    const { pid, seconds, signal } = await driven('urgent', 'trap "" TERM; sleep 60', [
      'SIGTERM',
      'SIGTERM',
    ])
    expect(signal).toBe('SIGTERM')
    expect(seconds).toBeLessThan(1.5)
    expect(alive(pid)).toBe(false)
  })
})
