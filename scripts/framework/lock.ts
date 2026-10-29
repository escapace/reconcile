import { linkSync, readFileSync, renameSync, rmSync, writeFileSync } from 'node:fs'
import { Blocked } from './command'
import { LOCK } from './paths'
import { startTime, stopGroup } from './processes'

/** A process told apart from a later one that reuses its number. */
export interface Process {
  readonly pid: number
  readonly started: string | undefined
}

/** Who holds the lock: the supervising process, what it runs and the process group of its
 * running step. */
export interface Holder {
  readonly command: string
  readonly group: Process | undefined
  readonly process: Process
  readonly since: string
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
      `another round is running: pid ${holder.process.pid} since ${holder.since} (${holder.command}). ` +
        `Wait for it to finish; rounds never overlap.`,
    )
  }
}

/** The guard a process holds while it takes over an abandoned lock. */
const GUARD = `${LOCK}.takeover`

const running = (owner: Process): boolean => startTime(owner.pid) === owner.started

/** Writes `holder` to a file of this process's own, so that the lock file appears complete. */
function staged(holder: Holder): string {
  const file = `${LOCK}.${process.pid}`
  writeFileSync(file, JSON.stringify(holder))
  return file
}

/** Creates `file` holding `holder` unless it exists. */
function create(file: string, holder: Holder): boolean {
  const source = staged(holder)
  try {
    linkSync(source, file)
    return true
  } catch (error) {
    if ((error as NodeJS.ErrnoException).code === 'EEXIST') return false
    throw error
  } finally {
    rmSync(source, { force: true })
  }
}

/** The holder that `file` records: undefined when there is no file, null when it cannot be read. */
function read(file: string): Holder | null | undefined {
  let text: string
  try {
    text = readFileSync(file, 'utf8')
  } catch (error) {
    if ((error as NodeJS.ErrnoException).code === 'ENOENT') return undefined
    throw error
  }
  try {
    return JSON.parse(text) as Holder
  } catch {
    return null
  }
}

const sameHolder = (left: Holder | null | undefined, right: Holder): boolean =>
  left?.process.pid === right.process.pid && left.process.started === right.process.started

/** Removes a lock whose holder died, after stopping its last step, unless another process is
 * already taking it over. */
async function takeOver(abandoned: Holder, holder: Holder): Promise<void> {
  if (!create(GUARD, holder)) {
    const guard = read(GUARD)
    if (guard !== null && guard !== undefined && running(guard.process))
      throw new Blocked('another round is taking over an abandoned lock; try again')
    rmSync(GUARD, { force: true })
    return
  }
  try {
    if (!sameHolder(read(LOCK), abandoned)) return
    const group = abandoned.group
    if (group !== undefined && running(group)) await stopGroup(group.pid)
    else if (group !== undefined)
      process.stderr.write(
        `The abandoned round's last step, process group ${group.pid}, may have left processes.\n`,
      )
    rmSync(LOCK, { force: true })
  } finally {
    rmSync(GUARD, { force: true })
  }
}

/** Takes the lock, or raises `LockBusy` while a live process holds it. */
async function acquire(holder: Holder): Promise<void> {
  for (let attempt = 0; attempt < 3; attempt += 1) {
    if (create(LOCK, holder)) return
    const current = read(LOCK)
    if (current === null)
      throw new Blocked(`the round lock ${LOCK} is unreadable; remove it if no round is running`)
    if (current !== undefined && running(current.process)) throw new LockBusy(current)
    if (current !== undefined) await takeOver(current, holder)
  }
  throw new Blocked(`cannot take the round lock at ${LOCK}; try again`)
}

/**
 * Runs `body` while holding the machine-wide round lock. A lock whose holder has died is taken
 * over after the process group of its last step is stopped; a lock held by a live process raises
 * `LockBusy`.
 */
export async function withLock<T>(command: string, body: (lock: Lock) => Promise<T>): Promise<T> {
  const self = { pid: process.pid, started: startTime(process.pid) }
  let holder: Holder = { command, group: undefined, process: self, since: new Date().toISOString() }
  await acquire(holder)
  const lock: Lock = {
    setGroup(group) {
      holder = {
        ...holder,
        group: group === undefined ? undefined : { pid: group, started: startTime(group) },
      }
      // A rename replaces the lock at once, so a reader never sees it half written.
      renameSync(staged(holder), LOCK)
    },
  }
  try {
    return await body(lock)
  } finally {
    if (sameHolder(read(LOCK), holder)) rmSync(LOCK, { force: true })
  }
}
