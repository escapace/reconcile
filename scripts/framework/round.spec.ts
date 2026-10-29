import { spawn } from 'node:child_process'
import { existsSync, mkdtempSync, readFileSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import path from 'node:path'
import { setTimeout as sleep } from 'node:timers/promises'
import { describe, expect, it } from 'vitest'

const state = mkdtempSync(path.join(tmpdir(), 'reconcile-round-spec-'))
process.env.RECONCILE_STATE = state
const { runRound } = await import('./round')

const shell = (name: string, script: string) => ({ command: ['sh', '-c', script], name })

/** Whether a process still runs: a killed one may linger as a zombie until it is reaped. */
const alive = (pid: number): boolean => {
  try {
    return !/^\d+ \(.*\) Z/.test(readFileSync(`/proc/${pid}/stat`, 'utf8'))
  } catch {
    return false
  }
}

const receiptOf = (file: string): Record<string, unknown> =>
  JSON.parse(readFileSync(file, 'utf8')) as Record<string, unknown>

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

  it('stops at the first step that fails and keeps its exit code', async () => {
    const result = await runRound({
      name: 'fail',
      steps: [shell('failing', 'exit 3'), shell('never', 'echo never')],
    })
    expect(result.status).toBe('failed')
    expect(result.exitCode).toBe(3)
    expect(result.steps).toHaveLength(1)
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

  it('records an interrupted round as cancelled and stops its step', async () => {
    const directory = mkdtempSync(path.join(state, 'cancel-'))
    const pidFile = path.join(directory, 'pid')
    // Outside the repository only the .mts extension makes the driver an ES module.
    const driver = path.join(directory, 'driver.mts')
    writeFileSync(
      driver,
      `import { runRound } from ${JSON.stringify(path.join(import.meta.dirname, 'round.ts'))}
const result = await runRound({ directory: ${JSON.stringify(directory)}, name: 'cancel', steps: [
  { command: ['sh', '-c', 'echo $$ > ${pidFile}; sleep 60'], name: 'sleeper' }] })
process.exitCode = result.exitCode\n`,
    )
    const child = spawn(process.execPath, ['--import', 'tsx', driver], {
      env: { ...process.env, RECONCILE_STATE: state },
      stdio: 'ignore',
    })
    const closed = new Promise<number | null>((resolve) => child.once('close', resolve))
    const started = (): boolean => existsSync(pidFile) && readFileSync(pidFile, 'utf8') !== ''
    while (child.exitCode === null && !started()) await sleep(50)
    child.kill('SIGINT')
    const code = await closed
    expect(code).toBe(130)
    expect(receiptOf(path.join(directory, 'receipt.json'))).toMatchObject({ status: 'cancelled' })
    expect(alive(Number(readFileSync(pidFile, 'utf8')))).toBe(false)
  })
})
