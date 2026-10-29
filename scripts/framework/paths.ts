import { homedir } from 'node:os'
import path from 'node:path'

/** The root of the checkout these tools belong to, or of the copy they run in. */
export const ROOT = path.resolve(import.meta.dirname, '../..')

/** Where rounds keep receipts, logs and recorded passes: outside the repository, per user. */
export const STATE =
  process.env.RECONCILE_STATE ??
  path.join(process.env.XDG_STATE_HOME ?? path.join(homedir(), '.local', 'state'), 'reconcile')

/** The lock every round holds, machine-wide, so that no two rounds overlap. */
export const LOCK = process.env.RECONCILE_LOCK ?? '/tmp/reconcile-round.lock'

/** A path a maintainer typed, resolved against the directory they ran the command in, which pnpm
 * passes as INIT_CWD, since it runs every script from the package root. */
export const fromUser = (value: string): string =>
  path.resolve(process.env.INIT_CWD ?? process.cwd(), value)
