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
const { identity } = await import('./processes')

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
    writeLock(process.pid, identity(process.pid))
    await expect(run()).rejects.toThrow(LockBusy)
    // A caller in another time zone sees the same holder.
    const zone = process.env.TZ
    process.env.TZ = 'Pacific/Kiritimati'
    try {
      await expect(run()).rejects.toThrow(LockBusy)
    } finally {
      if (zone === undefined) delete process.env.TZ
      else process.env.TZ = zone
    }
    writeFileSync(lockFile, '{"comm')
    await expect(run()).rejects.toThrow(Blocked)
  })

  it('takes over a lock whose holder died, after stopping its last step', async () => {
    const group = step()
    writeLock(deadPid(), 'then', group, identity(group))
    expect(await run()).toBe(true)
    for (let waited = 0; waited < 2000 && alive(group); waited += 50) await sleep(50)
    expect(alive(group)).toBe(false)
  })

  it('stops what remains of the last step when its leader died before its supervisor', async () => {
    const leader = spawn('sh', ['-c', 'sleep 60 & echo $!'], {
      detached: true,
      stdio: ['ignore', 'pipe', 'ignore'],
    })
    const member = Number(
      await new Promise<string>((resolve) => leader.stdout.once('data', resolve)),
    )
    const started = identity(leader.pid!)
    await new Promise((resolve) => leader.once('close', resolve))
    writeLock(deadPid(), 'then', leader.pid, started)
    expect(await run()).toBe(true)
    for (let waited = 0; waited < 2000 && alive(member); waited += 50) await sleep(50)
    expect(alive(member)).toBe(false)
  })

  it('removes the guard of a takeover whose process died, and refuses one it cannot read', async () => {
    writeLock(deadPid(), 'then')
    writeFileSync(
      `${lockFile}.takeover`,
      JSON.stringify({ process: { pid: deadPid(), started: 'then' } }),
    )
    expect(await run()).toBe(true)
    expect(existsSync(`${lockFile}.takeover`)).toBe(false)
    writeLock(deadPid(), 'then')
    writeFileSync(`${lockFile}.takeover`, '{"proc')
    try {
      await expect(run()).rejects.toThrow(/takeover guard .* is unreadable/)
    } finally {
      rmSync(`${lockFile}.takeover`, { force: true })
    }
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
