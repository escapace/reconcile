import { constants } from 'node:os'

// How the CLI ends when it is interrupted. The first SIGINT, SIGTERM or SIGHUP asks the running
// round to stop: its step is stopped, its receipt written and the lock released, and the CLI then
// ends by that signal, so that a shell sees it was interrupted. Each further signal stops the
// steps at once instead of after their grace period. Output to a reader that went away, as with
// `| head`, stops the run like an interrupt, and the CLI then exits 141. Node restores every
// signal's default action when it starts, so a SIGHUP that `nohup` ignored still interrupts.

const SIGNALS = ['SIGHUP', 'SIGINT', 'SIGTERM'] as const

/** The exit code of a CLI whose output reader went away, as if SIGPIPE had ended it. */
const OUTPUT_CLOSED = 128 + constants.signals.SIGPIPE

type Reason = 'output closed' | NodeJS.Signals

let received: Reason | undefined
let installed = false
const listeners = new Set<(urgent: boolean) => void>()

function interrupt(reason: Reason): void {
  const urgent = received !== undefined
  received ??= reason
  for (const listener of listeners) listener(urgent)
}

/** Treats a closed reader of the CLI's output as an interrupt, and its later writes as lost. */
function onOutputError(error: NodeJS.ErrnoException): void {
  if (error.code === 'EPIPE' || error.code === 'ERR_STREAM_DESTROYED') interrupt('output closed')
  else throw error
}

/** Handles interrupts for the rest of the CLI's life. Called once, by the CLI's entry point;
 * without it, rounds run until they end. */
export function handleInterrupts(): void {
  if (installed) return
  installed = true
  for (const signal of SIGNALS) process.on(signal, interrupt)
  process.stdout.on('error', onOutputError)
  process.stderr.on('error', onOutputError)
}

/** Whether the CLI was interrupted, and so should start nothing new. */
export const interrupted = (): boolean => received !== undefined

/** Whether the CLI's output still reaches a reader. */
export const outputOpen = (): boolean => received !== 'output closed'

/** Calls `listener` on each interrupt, `urgent` from the second on; returns its removal. */
export function onInterrupt(listener: (urgent: boolean) => void): () => void {
  listeners.add(listener)
  return () => listeners.delete(listener)
}

/** Ends the CLI with `code`, or, once interrupted, by the signal that interrupted it. */
export function finish(code: number): void {
  if (received === undefined) {
    process.exitCode = code
    return
  }
  if (received === 'output closed') {
    process.exitCode = OUTPUT_CLOSED
    return
  }
  for (const signal of SIGNALS) process.removeAllListeners(signal)
  process.kill(process.pid, received)
}
