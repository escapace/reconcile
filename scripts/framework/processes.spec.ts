import { spawn } from 'node:child_process'
import { setTimeout as sleep } from 'node:timers/promises'
import { describe, expect, it } from 'vitest'
import { groupAlive, identity, stopGroup } from './processes'

/** A process group whose leader ignores SIGTERM, as a stubborn step's would. */
function stubborn(): number {
  const child = spawn('sh', ['-c', 'trap "" TERM; sleep 60'], { detached: true, stdio: 'ignore' })
  return child.pid!
}

describe('identity', () => {
  it('names a running process alike in any time zone, and no process that has ended', async () => {
    const own = identity(process.pid)
    expect(own).toMatch(new RegExp(`^${process.pid}@`))
    const zone = process.env.TZ
    process.env.TZ = 'Asia/Kathmandu'
    try {
      expect(identity(process.pid)).toBe(own)
    } finally {
      if (zone === undefined) delete process.env.TZ
      else process.env.TZ = zone
    }
    const child = spawn('true')
    await new Promise((resolve) => child.once('close', resolve))
    expect(identity(child.pid!)).toBeUndefined()
  })

  it.runIf(process.platform === 'linux')('counts a zombie as ended', async () => {
    // The background sleep's parent execs into a process that never reaps it.
    const parent = spawn('sh', ['-c', 'sleep 0.1 & echo $!; exec sleep 5'], {
      stdio: ['ignore', 'pipe', 'ignore'],
    })
    const zombie = Number(
      await new Promise<string>((resolve) => parent.stdout.once('data', resolve)),
    )
    await sleep(400)
    try {
      expect(identity(zombie)).toBeUndefined()
    } finally {
      parent.kill('SIGKILL')
    }
  })
})

describe('stopGroup', () => {
  it('gives a group half a second to end on SIGTERM, or kills it at once when urgent', async () => {
    const patient = stubborn()
    await sleep(100)
    let started = performance.now()
    await stopGroup(patient)
    expect(performance.now() - started).toBeGreaterThanOrEqual(500)
    expect(groupAlive(patient)).toBe(false)
    const urgent = stubborn()
    await sleep(100)
    started = performance.now()
    await stopGroup(urgent, true)
    expect(performance.now() - started).toBeLessThan(450)
    expect(groupAlive(urgent)).toBe(false)
  })
})
