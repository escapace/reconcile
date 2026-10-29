import { spawnSync } from 'node:child_process'
import { readdirSync, readFileSync, readlinkSync } from 'node:fs'
import { setTimeout as sleep } from 'node:timers/promises'
import { Blocked } from './command'

// Processes as the supervisor sees them. On Linux they are read from /proc, which tells a live
// process from a zombie and gives each a start time that neither the time zone, the locale nor a
// change of the clock moves; elsewhere `ps` answers, read in UTC and the C locale.

const PROC = process.platform === 'linux'

/** The fields of /proc/<pid>/stat after the command name, which may itself hold spaces. */
function statFields(pid: number | string): string[] | undefined {
  let text: string
  try {
    text = readFileSync(`/proc/${pid}/stat`, 'utf8')
  } catch {
    return undefined
  }
  return text.slice(text.lastIndexOf(')') + 2).split(' ')
}

/** A zombie has exited and waits only to be reaped; a dead process is going away. */
const finished = (state: string): boolean => state === 'Z' || state === 'X' || state === 'x'

/** `ps` in a fixed time zone and locale, so that every caller reads a start time alike. */
function ps(arguments_: readonly string[]): string {
  const result = spawnSync('ps', arguments_, {
    encoding: 'utf8',
    env: { ...process.env, LC_ALL: 'C', TZ: 'UTC' },
  })
  if (result.error !== undefined) throw new Blocked(`cannot run ps: ${result.error.message}`)
  return result.status === 0 ? result.stdout.trim() : ''
}

/**
 * A running process's identity: its number with its start time, which tells it apart from a
 * later process that reuses the number. Undefined when no such process runs, a zombie included.
 */
export function identity(pid: number): string | undefined {
  if (PROC) {
    const fields = statFields(pid)
    // Field 3 is the state and field 22 the start time in clock ticks since boot.
    return fields === undefined || finished(fields[0]) ? undefined : `${pid}@${fields[19]}`
  }
  const [state = '', ...started] = ps(['-o', 'stat=,lstart=', '-p', String(pid)]).split(/\s+/)
  return state === '' || state.startsWith('Z') ? undefined : `${pid}@${started.join(' ')}`
}

/** Whether a process group still has a member that has not exited. */
export function groupAlive(group: number): boolean {
  if (!PROC) {
    try {
      process.kill(-group, 0)
      return true
    } catch {
      return false
    }
  }
  for (const entry of readdirSync('/proc')) {
    // Field 5 is the process group.
    const fields = /^\d+$/.test(entry) ? statFields(entry) : undefined
    if (fields?.[2] === String(group) && !finished(fields[0])) return true
  }
  return false
}

const signalGroup = (group: number, signal: NodeJS.Signals): void => {
  try {
    process.kill(-group, signal)
  } catch {
    // The group has already exited.
  }
}

/** Waits up to `ms` for a group to exit; returns whether it did. */
async function exited(group: number, ms: number): Promise<boolean> {
  for (let waited = 0; waited < ms; waited += 50) {
    if (!groupAlive(group)) return true
    await sleep(50)
  }
  return !groupAlive(group)
}

/** Stops every process left in a process group: SIGTERM, then SIGKILL to what remains half a
 * second later, or at once when `now` is set. */
export async function stopGroup(group: number | undefined, now = false): Promise<void> {
  if (group === undefined || !groupAlive(group)) return
  if (!now) {
    signalGroup(group, 'SIGTERM')
    if (await exited(group, 500)) return
  }
  signalGroup(group, 'SIGKILL')
  await exited(group, 1000)
}

/** The kernel's names of a process's standard output and error, such as `socket:[1234]`, read
 * as it starts, so that whatever later holds them open can be found. Only Linux can tell. */
export function outputsOf(pid: number | undefined): Set<string> {
  const outputs = new Set<string>()
  if (!PROC || pid === undefined) return outputs
  for (const fd of [1, 2])
    try {
      outputs.add(readlinkSync(`/proc/${pid}/fd/${fd}`))
    } catch {
      // The process has already ended.
    }
  return outputs
}

/** Kills every other process that holds one of `outputs` open, such as a step's descendant that
 * left its process group; returns how many it found. Only Linux can tell. */
export function killHolders(outputs: ReadonlySet<string>): number {
  if (!PROC || outputs.size === 0) return 0
  let killed = 0
  for (const entry of readdirSync('/proc')) {
    if (!/^\d+$/.test(entry) || Number(entry) === process.pid) continue
    let descriptors: string[]
    try {
      descriptors = readdirSync(`/proc/${entry}/fd`)
    } catch {
      continue
    }
    const holds = descriptors.some((fd) => {
      try {
        return outputs.has(readlinkSync(`/proc/${entry}/fd/${fd}`))
      } catch {
        return false
      }
    })
    if (!holds) continue
    try {
      process.kill(Number(entry), 'SIGKILL')
      killed += 1
    } catch {
      // It has already exited.
    }
  }
  return killed
}
