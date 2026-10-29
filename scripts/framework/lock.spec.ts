import { spawn, spawnSync } from 'node:child_process'
import { existsSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import path from 'node:path'
import { setTimeout as sleep } from 'node:timers/promises'
import { afterAll, afterEach, describe, expect, it } from 'vitest'

const directory = mkdtempSync(path.join(tmpdir(), 'reconcile-lock-spec-'))
const lockFile = path.join(directory, 'round.lock')
process.env.RECONCILE_LOCK = lockFile
const { Blocked } = await import('./command')
const { LockBusy, withLock } = await import('./lock')
const { startTime } = await import('./processes')

/** Whether a process still runs: a killed one may linger as a zombie until it is reaped. */
const alive = (pid: number): boolean => {
  const stat = spawnSync('ps', ['-o', 'stat=', '-p', String(pid)], {
    encoding: 'utf8',
  }).stdout.trim()
  return stat !== '' && !stat.startsWith('Z')
}

/** A process number that no process holds now. */
const deadPid = (): number =>
  Number(spawnSync('sh', ['-c', 'echo $$'], { encoding: 'utf8' }).stdout)

/** A lock file as a supervisor writes it. */
function writeLock(
  pid: number,
  started: string | undefined,
  group?: number,
  groupStarted?: string,
): void {
  const holder = {
    command: 'other',
    group: group === undefined ? undefined : { pid: group, started: groupStarted },
    process: { pid, started },
    since: 'then',
  }
  writeFileSync(lockFile, JSON.stringify(holder))
}

/** A process in a process group of its own, as a supervisor starts each step. */
const step = (): number => spawn('sleep', ['60'], { detached: true, stdio: 'ignore' }).pid!

const run = async (): Promise<boolean> =>
  await withLock('spec', async () => await Promise.resolve(true))

afterEach(() => {
  rmSync(lockFile, { force: true })
})

afterAll(() => {
  rmSync(directory, { force: true, recursive: true })
})

describe('withLock', () => {
  it('holds the lock while its body runs and releases it after', async () => {
    const held = await withLock('spec', async () => await Promise.resolve(existsSync(lockFile)))
    expect(held).toBe(true)
    expect(existsSync(lockFile)).toBe(false)
  })

  it('refuses a lock that a live process holds, and one it cannot read', async () => {
    writeLock(process.pid, startTime(process.pid))
    await expect(run()).rejects.toThrow(LockBusy)
    writeFileSync(lockFile, '{"comm')
    await expect(run()).rejects.toThrow(Blocked)
  })

  it('takes over a lock whose holder died, after stopping its last step', async () => {
    const group = step()
    writeLock(deadPid(), 'then', group, startTime(group))
    expect(await run()).toBe(true)
    for (let waited = 0; waited < 2000 && alive(group); waited += 50) await sleep(50)
    expect(alive(group)).toBe(false)
  })

  it('takes over a lock whose number another process now holds', async () => {
    writeLock(process.pid, 'an earlier start')
    expect(await run()).toBe(true)
  })

  it('leaves alone a process group that reuses the number of the abandoned step', async () => {
    const group = step()
    try {
      writeLock(deadPid(), 'then', group, 'an earlier start')
      expect(await run()).toBe(true)
      expect(alive(group)).toBe(true)
    } finally {
      process.kill(-group, 'SIGKILL')
    }
  })
})
