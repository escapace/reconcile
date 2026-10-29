import { openSync, readFileSync, rmSync, writeFileSync, writeSync, closeSync } from 'node:fs'
import { Blocked } from './command'
import { LOCK } from './paths'

/** Who holds the lock: the supervising process and the process group of its running step. */
export interface Holder {
  readonly command: string
  readonly group: number | undefined
  readonly pid: number
  readonly started: string
}

/** The lock a supervisor holds; it names each step's process group, so that whoever takes over
 * a lock its holder abandoned can stop that step first. */
export interface Lock {
  readonly setGroup: (group: number | undefined) => void
}

/** Raised when another live process holds the lock. */
export class LockBusy extends Blocked {
  constructor(holder: Holder) {
    super(
      `another round is running: pid ${holder.pid} since ${holder.started} (${holder.command}). ` +
        `Wait for it to finish; rounds never overlap.`,
    )
  }
}

const alive = (pid: number): boolean => {
  try {
    process.kill(pid, 0)
    return true
  } catch (error) {
    return (error as NodeJS.ErrnoException).code === 'EPERM'
  }
}

const killGroup = (group: number): void => {
  try {
    process.kill(-group, 'SIGKILL')
  } catch {
    // The group has already exited.
  }
}

const read = (): Holder | undefined => {
  try {
    return JSON.parse(readFileSync(LOCK, 'utf8')) as Holder
  } catch {
    return undefined
  }
}

function create(holder: Holder): boolean {
  let descriptor: number
  try {
    descriptor = openSync(LOCK, 'wx')
  } catch (error) {
    if ((error as NodeJS.ErrnoException).code === 'EEXIST') return false
    throw error
  }
  writeSync(descriptor, JSON.stringify(holder))
  closeSync(descriptor)
  return true
}

/**
 * Runs `body` while holding the machine-wide round lock. A lock whose holder has died is taken
 * over after the process group of its last step is killed; a lock held by a live process raises
 * `LockBusy`.
 */
export async function withLock<T>(command: string, body: (lock: Lock) => Promise<T>): Promise<T> {
  let holder: Holder = {
    command,
    group: undefined,
    pid: process.pid,
    started: new Date().toISOString(),
  }
  for (let attempt = 0; !create(holder); attempt += 1) {
    const current = read()
    if (current !== undefined && alive(current.pid)) throw new LockBusy(current)
    if (attempt > 0) throw new Error(`cannot take over the round lock at ${LOCK}`)
    if (current?.group !== undefined) killGroup(current.group)
    rmSync(LOCK, { force: true })
  }
  const lock: Lock = {
    setGroup(group) {
      holder = { ...holder, group }
      writeFileSync(LOCK, JSON.stringify(holder))
    },
  }
  try {
    return await body(lock)
  } finally {
    if (read()?.pid === process.pid) rmSync(LOCK, { force: true })
  }
}
