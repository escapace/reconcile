import { linkSync, readFileSync, renameSync, rmSync, writeFileSync } from 'node:fs'
import { Blocked } from './command'
import { LOCK } from './paths'
import { groupAlive, identity, stopGroup } from './processes'

/** A process told apart from a later one that reuses its number: `started` is its identity,
 * undefined when it had already ended when it was recorded. */
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

const running = (owner: Process): boolean =>
  owner.started !== undefined && identity(owner.pid) === owner.started

/**
 * Whether the abandoned step's process group still runs: its leader is the process recorded, or
 * the leader is gone but members remain. While any member remains, the kernel gives no new
 * process the group's number, so those members are the step's.
 */
function stepRuns(group: Process): boolean {
  const leader = identity(group.pid)
  return leader === undefined ? groupAlive(group.pid) : leader === group.started
}

/** Writes `holder` to a file of this process's own, so that the lock file appears complete. */
function staged(holder: Holder): string {
  const file = `${LOCK}.${process.pid}`
  writeFileSync(file, JSON.stringify(holder))
  return file
}

/** Replaces `file` with `holder` at once, so that a reader never sees it half written. */
function replace(file: string, holder: Holder): void {
  const source = staged(holder)
  try {
    renameSync(source, file)
  } catch (error) {
    rmSync(source, { force: true })
    throw error
  }
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

/** Removes `file` if it still records `holder`. Moving it aside first makes the check and the
 * removal one step: a file another process wrote meanwhile is put back. */
function removeIf(file: string, holder: Holder): void {
  const aside = `${file}.${process.pid}.removed`
  try {
    renameSync(file, aside)
  } catch (error) {
    if ((error as NodeJS.ErrnoException).code === 'ENOENT') return
    throw error
  }
  if (!sameHolder(read(aside), holder))
    try {
      linkSync(aside, file)
    } catch {
      // A newer file took its place; that one stands.
    }
  rmSync(aside, { force: true })
}

/** Removes a lock whose holder died, after stopping its last step, unless another process is
 * already taking it over. */
async function takeOver(abandoned: Holder, holder: Holder): Promise<void> {
  if (!create(GUARD, holder)) {
    const guard = read(GUARD)
    if (guard === undefined) return
    if (guard === null)
      throw new Blocked(
        `the takeover guard ${GUARD} is unreadable; remove it if no round is running`,
      )
    if (running(guard.process))
      throw new Blocked('another round is taking over an abandoned lock; try again')
    // A taker that died left its guard.
    removeIf(GUARD, guard)
    return
  }
  try {
    if (!sameHolder(read(LOCK), abandoned)) return
    const group = abandoned.group
    if (group !== undefined && stepRuns(group)) await stopGroup(group.pid)
    removeIf(LOCK, abandoned)
  } finally {
    removeIf(GUARD, holder)
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
  const self = { pid: process.pid, started: identity(process.pid) }
  let holder: Holder = { command, group: undefined, process: self, since: new Date().toISOString() }
  await acquire(holder)
  const lock: Lock = {
    setGroup(group) {
      holder = {
        ...holder,
        group: group === undefined ? undefined : { pid: group, started: identity(group) },
      }
      replace(LOCK, holder)
    },
  }
  try {
    return await body(lock)
  } finally {
    removeIf(LOCK, holder)
  }
}
