import { spawn, spawnSync } from 'node:child_process'
import { existsSync, mkdtempSync, readFileSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import path from 'node:path'
import { setTimeout as sleep } from 'node:timers/promises'
import { describe, expect, it } from 'vitest'

const lockFile = path.join(mkdtempSync(path.join(tmpdir(), 'reconcile-lock-spec-')), 'round.lock')
process.env.RECONCILE_LOCK = lockFile
const { LockBusy, withLock } = await import('./lock')

/** Whether a process still runs: a killed one may linger as a zombie until it is reaped. */
const alive = (pid: number): boolean => {
  try {
    return !/^\d+ \(.*\) Z/.test(readFileSync(`/proc/${pid}/stat`, 'utf8'))
  } catch {
    return false
  }
}

describe('withLock', () => {
  it('holds the lock while its body runs and releases it after', async () => {
    const held = await withLock('spec', async () => await Promise.resolve(existsSync(lockFile)))
    expect(held).toBe(true)
    expect(existsSync(lockFile)).toBe(false)
  })

  it('refuses a lock that a live process holds', async () => {
    const holder = { command: 'other', group: undefined, pid: process.pid, started: 'now' }
    writeFileSync(lockFile, JSON.stringify(holder))
    try {
      await expect(withLock('spec', async () => await Promise.resolve(0))).rejects.toThrow(LockBusy)
    } finally {
      spawnSync('rm', ['-f', lockFile])
    }
  })

  it('takes over a lock whose holder died, after stopping its last step', async () => {
    const dead = spawnSync('sh', ['-c', 'echo $$'], { encoding: 'utf8' })
    const step = spawn('sleep', ['60'], { detached: true, stdio: 'ignore' })
    writeFileSync(
      lockFile,
      JSON.stringify({
        command: 'gone',
        group: step.pid,
        pid: Number(dead.stdout),
        started: 'then',
      }),
    )
    const ran = await withLock('spec', async () => await Promise.resolve(true))
    expect(ran).toBe(true)
    for (let waited = 0; waited < 2000 && alive(step.pid!); waited += 50) await sleep(50)
    expect(alive(step.pid!)).toBe(false)
  })
})
