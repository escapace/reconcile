import { spawnSync } from 'node:child_process'
import { setTimeout as sleep } from 'node:timers/promises'
import { Blocked } from './command'

const groupAlive = (group: number): boolean => {
  try {
    process.kill(-group, 0)
    return true
  } catch {
    return false
  }
}

const signalGroup = (group: number, signal: NodeJS.Signals): void => {
  try {
    process.kill(-group, signal)
  } catch {
    // The group has already exited.
  }
}

/** Stops every process left in a process group: SIGTERM, then SIGKILL half a second later. */
export async function stopGroup(group: number | undefined): Promise<void> {
  if (group === undefined || !groupAlive(group)) return
  signalGroup(group, 'SIGTERM')
  await sleep(500)
  signalGroup(group, 'SIGKILL')
  for (let waited = 0; waited < 1000 && groupAlive(group); waited += 50) await sleep(50)
}

/** When a process started, as `ps` reports it, or undefined when no such process exists. With
 * its number, the start time tells a process apart from a later one that reuses that number. */
export function startTime(pid: number): string | undefined {
  const result = spawnSync('ps', ['-o', 'lstart=', '-p', String(pid)], { encoding: 'utf8' })
  if (result.error !== undefined) throw new Blocked(`cannot run ps: ${result.error.message}`)
  const started = result.stdout.trim()
  return result.status === 0 && started !== '' ? started : undefined
}
