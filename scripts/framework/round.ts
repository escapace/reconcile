import { spawn } from 'node:child_process'
import {
  createWriteStream,
  mkdirSync,
  readFileSync,
  writeFileSync,
  type WriteStream,
} from 'node:fs'
import { constants } from 'node:os'
import path from 'node:path'
import type { Lock } from './lock'
import { ROOT, STATE } from './paths'
import { stopGroup } from './processes'

/** Every round's budget: the 300 seconds a round may take, less a margin for shutdown. */
export const BUDGET_SECONDS = 295

/** The part of the budget kept back for stopping the last step's processes. */
const SHUTDOWN_RESERVE_MS = 2000

/** How a round or step ended. */
export type Status = 'cancelled' | 'failed' | 'passed' | 'timed_out'

/** The exit code of a round with each status: a timeout is incomplete, not a failure. A step's
 * own exit code is kept in the receipt. */
const EXIT_CODES: Record<Status, number> = { cancelled: 130, failed: 1, passed: 0, timed_out: 124 }

/** One command of a round, run in its own process group. */
export interface Step {
  readonly command: readonly string[]
  readonly name: string
  readonly cwd?: string
  /** Variables added to the environment; a function is called when the step starts, within the
   * round's budget, and a step whose function throws fails. Every step also gets
   * `RECONCILE_DEADLINE`, the time in epoch milliseconds by which it must have ended. */
  readonly env?: (() => Readonly<Record<string, string>>) | Readonly<Record<string, string>>
}

export interface StepResult {
  readonly command: readonly string[]
  readonly elapsedSeconds: number
  readonly exitCode: number
  readonly log: string
  readonly name: string
  readonly status: Status
}

export interface Round {
  readonly name: string
  readonly steps: readonly Step[]
  readonly budgetSeconds?: number
  /** The directory for the round's logs and receipt; by default a new one under the state. */
  readonly directory?: string
  readonly lock?: Lock
  /** Extra fields for the receipt, such as the inputs the round ran on. */
  readonly record?: Readonly<Record<string, unknown>>
  /** Print each step's output as it runs, rather than only on failure. */
  readonly stream?: boolean
}

export interface RoundResult {
  readonly directory: string
  readonly elapsedSeconds: number
  readonly exitCode: number
  readonly receipt: string
  readonly status: Status
  readonly steps: readonly StepResult[]
}

const seconds = (since: number): number => Math.round((performance.now() - since) / 100) / 10

/** A new directory under `parent` named after the time and `name`, such as one for a round's
 * logs and receipt. */
export function stampedDirectory(name: string, parent = path.join(STATE, 'runs')): string {
  const stamp = new Date().toISOString().replaceAll(/[:.]/g, '-')
  const base = path.join(parent, `${stamp}-${name.replaceAll(/[^a-z0-9]+/gi, '-')}`)
  mkdirSync(path.dirname(base), { recursive: true })
  for (let suffix = 1; ; suffix += 1) {
    const candidate = suffix === 1 ? base : `${base}-${suffix}`
    try {
      mkdirSync(candidate)
      return candidate
    } catch (error) {
      if ((error as NodeJS.ErrnoException).code !== 'EEXIST') throw error
    }
  }
}

/** The last lines of a log, to show what failed. */
function tail(file: string, lines = 40): string {
  const text = readFileSync(file, 'utf8').trimEnd()
  return text.split('\n').slice(-lines).join('\n')
}

/** What a round's steps share: whether it was cancelled, the group of the step running now and
 * the lock that records that group. */
interface Control {
  cancelled: boolean
  group: number | undefined
  readonly lock: Lock | undefined
}

const setGroup = (control: Control, group: number | undefined): void => {
  control.group = group
  control.lock?.setGroup(group)
}

interface Ending {
  readonly code: number | null
  readonly signal: NodeJS.Signals | null
}

/** Starts a step in its own process group, writing its output to `output` and, when `echo` is
 * set, to this process's own. */
function launch(
  step: Step,
  output: WriteStream,
  echo: boolean,
  deadline: number,
): { ended: Promise<Ending>; group: number | undefined } {
  let environment: NodeJS.ProcessEnv
  try {
    environment = {
      ...process.env,
      ...(typeof step.env === 'function' ? step.env() : step.env),
      RECONCILE_DEADLINE: String(Math.round(Date.now() + deadline - performance.now())),
    }
  } catch (error) {
    output.write(`${(error as Error).message}\n`)
    return { ended: Promise.resolve({ code: 1, signal: null }), group: undefined }
  }
  const child = spawn(step.command[0], step.command.slice(1), {
    cwd: step.cwd ?? ROOT,
    detached: true,
    env: environment,
    stdio: ['ignore', 'pipe', 'pipe'],
  })
  const ended = new Promise<Ending>((resolve) => {
    child.once('error', (error) => {
      output.write(`cannot run ${step.command[0]}: ${error.message}\n`)
      resolve({ code: 127, signal: null })
    })
    child.once('close', (code, signal) => resolve({ code, signal }))
  })
  // Descendants that keep the pipes open would otherwise hold `close` back after the step exits.
  child.once('exit', () => void stopGroup(child.pid))
  child.stdout.on('data', (chunk: Buffer) => {
    output.write(chunk)
    if (echo) process.stdout.write(chunk)
  })
  child.stderr.on('data', (chunk: Buffer) => {
    output.write(chunk)
    if (echo) process.stderr.write(chunk)
  })
  return { ended, group: child.pid }
}

function stepStatus(code: number | null, timedOut: boolean, cancelled: boolean): Status {
  if (cancelled) return 'cancelled'
  if (timedOut) return 'timed_out'
  return code === 0 ? 'passed' : 'failed'
}

/** Runs one step in its own process group until it ends, the deadline passes or the round is
 * cancelled, then stops whatever it left running. */
async function runStep(
  step: Step,
  log: string,
  deadline: number,
  control: Control,
  echo: boolean,
): Promise<StepResult> {
  const started = performance.now()
  const output = createWriteStream(log)
  const { ended, group } = launch(step, output, echo, deadline)
  setGroup(control, group)
  let timedOut = false
  const timer = setTimeout(
    () => {
      timedOut = true
      void stopGroup(group)
    },
    Math.max(0, deadline - performance.now()),
  )
  const { code, signal } = await ended
  clearTimeout(timer)
  await stopGroup(group)
  setGroup(control, undefined)
  await new Promise<void>((resolve) => output.end(resolve))
  const status = stepStatus(code, timedOut, control.cancelled)
  return {
    command: step.command,
    elapsedSeconds: seconds(started),
    exitCode: code ?? 128 + (signal === null ? 0 : constants.signals[signal]),
    log,
    name: step.name,
    status,
  }
}

const verdicts: Record<Status, string> = {
  cancelled: 'CANCELLED',
  failed: 'FAILED',
  passed: 'ok',
  timed_out: 'INCOMPLETE (budget exhausted)',
}

/** Runs a step, showing a line for it and, if it fails, the end of its log; a streamed step
 * shows its own output instead. */
async function reportStep(
  step: Step,
  log: string,
  deadline: number,
  control: Control,
  round: Round,
): Promise<StepResult> {
  if (round.stream === true) return await runStep(step, log, deadline, control, true)
  process.stdout.write(`  ${step.name} ... `)
  const result = await runStep(step, log, deadline, control, false)
  process.stdout.write(`${verdicts[result.status]} (${result.elapsedSeconds} s)\n`)
  if (result.status === 'failed') process.stdout.write(`${tail(log)}\nLog: ${log}\n`)
  return result
}

const SIGNALS = ['SIGHUP', 'SIGINT', 'SIGTERM'] as const

/** Runs the steps in order until one does not pass, the deadline passes or a signal cancels the
 * round. */
async function runSteps(
  round: Round,
  directory: string,
  deadline: number,
): Promise<{ cancelled: boolean; steps: StepResult[] }> {
  const control: Control = { cancelled: false, group: undefined, lock: round.lock }
  const cancel = (): void => {
    control.cancelled = true
    void stopGroup(control.group)
  }
  for (const signal of SIGNALS) process.on(signal, cancel)
  const steps: StepResult[] = []
  try {
    for (const [index, step] of round.steps.entries()) {
      if (control.cancelled || performance.now() >= deadline) break
      const log = path.join(
        directory,
        `${index + 1}-${step.name.replaceAll(/[^a-z0-9]+/gi, '-')}.log`,
      )
      const result = await reportStep(step, log, deadline, control, round)
      steps.push(result)
      if (result.status !== 'passed') break
    }
  } finally {
    for (const signal of SIGNALS) process.off(signal, cancel)
  }
  return { cancelled: control.cancelled, steps }
}

/** A round's status: its last step's if that did not pass, else cancelled, out of budget before
 * its last step, or passed. */
function roundStatus(steps: readonly StepResult[], planned: number, cancelled: boolean): Status {
  const last = steps.at(-1)
  if (last !== undefined && last.status !== 'passed') return last.status
  if (cancelled) return 'cancelled'
  return steps.length < planned ? 'timed_out' : 'passed'
}

function budgetOf(round: Round): number {
  const budget = round.budgetSeconds ?? BUDGET_SECONDS
  if (!Number.isInteger(budget) || budget < 3 || budget > 300)
    throw new RangeError(`a round's budget must be 3 to 300 seconds, not ${budget}`)
  return budget
}

/**
 * Runs the steps of one round, in order, within one budget. Each step runs in its own process
 * group, which is stopped when the step ends, when the budget runs out and when the round is
 * interrupted. The round stops at the first step that does not pass and writes a receipt that is
 * never overwritten.
 */
export async function runRound(round: Round): Promise<RoundResult> {
  const budgetSeconds = budgetOf(round)
  const started = performance.now()
  const startedAt = new Date().toISOString()
  const directory = round.directory ?? stampedDirectory(round.name)
  mkdirSync(directory, { recursive: true })
  const deadline = started + budgetSeconds * 1000 - SHUTDOWN_RESERVE_MS
  const { cancelled, steps } = await runSteps(round, directory, deadline)
  const status = roundStatus(steps, round.steps.length, cancelled)
  const exitCode = EXIT_CODES[status]
  const elapsedSeconds = seconds(started)
  const receipt = path.join(directory, 'receipt.json')
  const fields = {
    budgetSeconds,
    elapsedSeconds,
    exitCode,
    name: round.name,
    startedAt,
    status,
    steps,
  }
  writeFileSync(receipt, `${JSON.stringify({ ...fields, ...round.record }, undefined, 2)}\n`, {
    flag: 'wx',
  })
  return { directory, elapsedSeconds, exitCode, receipt, status, steps }
}
