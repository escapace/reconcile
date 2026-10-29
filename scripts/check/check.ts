import { UsageError, type Command, type Parsed } from '../framework/command'
import { changedEnvironment, changedFiles, inputs, type Inputs } from '../framework/fingerprint'
import { withLock, type Lock } from '../framework/lock'
import { BUDGET_SECONDS, roundDirectory, runRound, type Status } from '../framework/round'
import { STATE } from '../framework/paths'
import { mutantNames } from './mutants'
import { findPass, latestPass, recordPass, type Pass } from './passes'
import { ROUNDS, type RoundDefinition, type RoundOptions } from './rounds'

const list = (names: readonly string[], limit = 3): string =>
  names.length <= limit
    ? names.join(', ')
    : `${names.slice(0, limit).join(', ')} and ${names.length - limit} more`

const described = (label: string, names: readonly string[]): string[] =>
  names.length === 0 ? [] : [`${label}: ${list(names)}`]

/** Why a round must run although it passed before: what changed since its latest pass. */
function reason(round: RoundDefinition, current: Inputs): string {
  const latest = latestPass(round.name)
  if (latest === undefined) return 'no pass recorded'
  const parts = [
    ...described('changed since its last pass', changedFiles(latest.files, current.files)),
    ...described(
      'environment changed',
      changedEnvironment(latest.environment, current.environment),
    ),
  ]
  return parts.length === 0 ? 'its inputs differ from its last pass' : parts.join('; ')
}

/** Whether a round reuses the pass recorded on `current`, and if not, why it runs. */
function decide(
  round: RoundDefinition,
  options: RoundOptions,
  fresh: boolean,
  current: Inputs,
): { pass: Pass | undefined; why: string } {
  if (round.narrowed(options)) return { pass: undefined, why: 'narrowed run; records no pass' }
  if (fresh) return { pass: undefined, why: '--fresh' }
  const pass = findPass(round.name, current.hash)
  return { pass, why: pass === undefined ? reason(round, current) : '' }
}

/** The exit code of an interrupted round. */
const EXIT_CANCELLED = 130

const verdicts: Record<Status, string> = {
  cancelled: 'CANCELLED',
  failed: 'FAILED',
  passed: 'passed',
  timed_out: 'INCOMPLETE: out of budget; rerun the whole round',
}

function roundNamed(name: string): RoundDefinition {
  const round = ROUNDS.find((candidate) => candidate.name === name)
  if (round === undefined)
    throw new UsageError(
      `unknown round "${name}"; the rounds are ${ROUNDS.map((known) => known.name).join(', ')}`,
    )
  return round
}

/** What each selected round would do, and why; runs nothing. */
function plan(rounds: readonly RoundDefinition[], options: RoundOptions, fresh: boolean): number {
  const width = Math.max(...rounds.map((round) => round.name.length)) + 2
  for (const round of rounds) {
    const { pass, why } = decide(round, options, fresh, inputs(round.exclude))
    const line =
      pass === undefined ? `run    ${why}` : `reuse  passed ${pass.finishedAt} on identical inputs`
    process.stdout.write(`${round.name.padEnd(width)}${line}\n`)
  }
  return 0
}

/** Records a pass on the inputs the round leaves behind, unless a file it does not declare as
 * its output changed while it ran. */
function record(round: RoundDefinition, before: Inputs, receipt: string): void {
  const after = inputs(round.exclude)
  const environment = changedEnvironment(before.environment, after.environment)
  if (environment.length > 0) {
    process.stdout.write(
      `${round.name}: the environment changed while it ran (${list(environment)}); no pass recorded\n`,
    )
    return
  }
  const changed = changedFiles(before.files, after.files)
  const outputs = round.outputs ?? []
  const rewritten = changed.filter((file) => outputs.includes(file))
  const foreign = changed.filter((file) => !outputs.includes(file))
  if (rewritten.length > 0)
    process.stdout.write(
      `${round.name}: the round rewrote ${list(rewritten)}; review and commit it\n`,
    )
  if (foreign.length > 0) {
    process.stdout.write(
      `${round.name}: files changed while it ran (${list(foreign)}); no pass recorded\n`,
    )
    return
  }
  recordPass(round.name, after, receipt)
}

/** Runs one round unless it passed on identical inputs; returns its exit code. */
async function runOne(
  round: RoundDefinition,
  options: RoundOptions,
  fresh: boolean,
  lock: Lock,
): Promise<number> {
  const before = inputs(round.exclude)
  const { pass, why } = decide(round, options, fresh, before)
  if (pass !== undefined) {
    process.stdout.write(`${round.name}: reused; passed ${pass.finishedAt} on identical inputs\n`)
    return 0
  }
  process.stdout.write(`${round.name}: running (${why})\n`)
  const narrowed = round.narrowed(options)
  const directory = roundDirectory(`check-${round.name}`)
  const result = await runRound({
    directory,
    lock,
    name: `check ${round.name}`,
    record: { inputs: { environment: before.environment, hash: before.hash }, narrowed },
    steps: round.steps(options, directory),
  })
  if (result.status === 'passed' && !narrowed) record(round, before, result.receipt)
  process.stdout.write(
    `${round.name}: ${verdicts[result.status]} in ${result.elapsedSeconds} s; receipt ${result.receipt}\n`,
  )
  return result.exitCode
}

/** The options of a run: only the mutants round takes mutant names and a seed count. */
function optionsFor(
  round: string | undefined,
  names: readonly string[],
  seeds: string | undefined,
): RoundOptions {
  if (names.length > 0 && round !== 'mutants')
    throw new UsageError(`only the mutants round takes names, not "${round}"`)
  const unknown = names.filter((name) => !mutantNames.includes(name))
  if (unknown.length > 0)
    throw new UsageError(
      `unknown mutants: ${unknown.join(', ')}; the mutants are ${mutantNames.join(', ')}`,
    )
  if (seeds === undefined) return { names, seeds }
  if (round !== 'mutants')
    throw new UsageError(
      '--seeds applies only to the mutants round: pnpm check mutants --seeds <n>',
    )
  if (!/^[1-9]\d*$/.test(seeds))
    throw new UsageError(`--seeds takes a positive integer, not "${seeds}"`)
  return { names, seeds }
}

/** Runs the rounds in order and returns the first failure's exit code; stops there unless
 * `keepGoing` is set. */
async function runAll(
  rounds: readonly RoundDefinition[],
  options: RoundOptions,
  fresh: boolean,
  keepGoing: boolean,
): Promise<number> {
  const invocation = ['pnpm check', ...process.argv.slice(3)].join(' ')
  return await withLock(invocation, async (lock) => {
    let failed = 0
    for (const round of rounds) {
      const code = await runOne(round, options, fresh, lock)
      if (failed === 0) failed = code
      // An interrupted round stops the run, --keep-going or not.
      if (code === EXIT_CANCELLED || (code !== 0 && !keepGoing)) break
    }
    return failed
  })
}

async function run({ positionals, values }: Parsed): Promise<number> {
  const [name, ...names] = positionals
  const rounds = name === undefined ? ROUNDS : [roundNamed(name)]
  // A string option that is not `multiple` parses to a string.
  const options = optionsFor(name, names, values.seeds as string | undefined)
  const fresh = values.fresh === true
  if (values.plan === true) return plan(rounds, options, fresh)
  return await runAll(rounds, options, fresh, values['keep-going'] === true)
}

export const check: Command = {
  description: [
    'A round is reused when it passed on identical inputs: the content and executable bit of ' +
      'every file of the working tree it does not exclude, tracked or untracked but not ignored, ' +
      'plus the platform, the Node version, the installed dependencies and NODE_OPTIONS. ' +
      '`--plan` shows what changed. The run stops at the first round that does not pass.',
    `Each round runs within a ${BUDGET_SECONDS}-second budget and holds a machine-wide lock, so ` +
      `no two rounds of check or bench overlap. Receipts and logs are kept under ${STATE}/runs.`,
    'Exit codes: 0 passed, 1 failed, 2 usage error, 3 could not start, 124 out of budget ' +
      '(incomplete; rerun the whole round), 130 interrupted.',
  ],
  examples: [
    'pnpm check                  # every round that has not passed on its current inputs',
    'pnpm check --plan           # what would run, and why',
    'pnpm check lean             # one round',
    'pnpm check mutants own-node-pins-dropped',
  ],
  name: 'check',
  options: {
    'fresh': {
      description: 'Run rounds even when a pass on identical inputs is recorded.',
      type: 'boolean',
    },
    'keep-going': {
      description: 'Run the remaining rounds after one does not pass.',
      type: 'boolean',
    },
    'plan': { description: 'Show which rounds would run and why; run nothing.', type: 'boolean' },
    'seeds': {
      description: 'mutants: seeds per bridge run. Any count but 1500 records no pass.',
      placeholder: '<n>',
      type: 'string',
    },
  },
  run,
  sections: [
    { rows: ROUNDS.map((round) => [round.name, round.summary] as const), title: 'Rounds' },
  ],
  summary: 'Is the change correct? Runs every round that has not passed on its current inputs.',
  usage: '[round [mutant...]] [options]',
}
