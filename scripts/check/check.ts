import { UsageError, type Command, type Parsed } from '../framework/command'
import { changedEnvironment, changedFiles, inputs, type Inputs } from '../framework/tree'
import { withLock, type Lock } from '../framework/lock'
import { interrupted } from '../framework/interrupt'
import {
  BUDGET_SECONDS,
  EXIT_CODES,
  stampedDirectory,
  runRound,
  type Status,
} from '../framework/round'
import { STATE } from '../framework/paths'
import { BRIDGES } from './bridges'
import { parseSeeds } from './bridges/selection'
import { findPass, latestPass, recordPass, type Pass } from './passes'
import { narrowed, ROUNDS, type RoundDefinition, type RoundOptions } from './rounds'

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
  if (narrowed(options)) return { pass: undefined, why: 'narrowed run; records no pass' }
  if (fresh) return { pass: undefined, why: '--fresh' }
  const pass = findPass(round.name, current.hash)
  return { pass, why: pass === undefined ? reason(round, current) : '' }
}

const verdicts: Record<Status, string> = {
  blocked: 'COULD NOT START',
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

/** What changed while a round ran, besides the files it declares as its outputs, which it may
 * rewrite; empty when nothing did. */
function changedWhileRunning(round: RoundDefinition, before: Inputs, after: Inputs): string[] {
  const outputs = round.outputs ?? []
  const changed = changedFiles(before.files, after.files)
  const rewritten = changed.filter((file) => outputs.includes(file))
  if (rewritten.length > 0)
    process.stdout.write(
      `${round.name}: the round rewrote ${list(rewritten)}; review and commit it\n`,
    )
  return [
    ...changed.filter((file) => !outputs.includes(file)),
    ...changedEnvironment(before.environment, after.environment).map(
      (key) => `the ${key} environment`,
    ),
  ]
}

/** The outcome of a round that passed: complete, and recorded as a pass unless it was narrowed,
 * when its inputs are those it started with; incomplete when they changed while it ran, since it
 * then validated a tree that no longer exists. */
function settle(round: RoundDefinition, before: Inputs, receipt: string, partial: boolean): number {
  const after = inputs(round.exclude)
  const changed = changedWhileRunning(round, before, after)
  if (changed.length > 0) {
    process.stdout.write(
      `${round.name}: INCOMPLETE: ${list(changed)} changed while it ran; rerun it\n`,
    )
    return EXIT_CODES.timed_out
  }
  if (!partial) recordPass(round.name, after, receipt)
  return 0
}

/** Runs one round unless it passed on identical inputs; returns its exit code. */
async function runOne(
  round: RoundDefinition,
  options: RoundOptions,
  fresh: boolean,
  lock: Lock,
): Promise<number> {
  if (interrupted()) return EXIT_CODES.cancelled
  const before = inputs(round.exclude)
  const { pass, why } = decide(round, options, fresh, before)
  if (pass !== undefined) {
    process.stdout.write(`${round.name}: reused; passed ${pass.finishedAt} on identical inputs\n`)
    return 0
  }
  process.stdout.write(`${round.name}: running (${why})\n`)
  const partial = narrowed(options)
  const directory = stampedDirectory(`check-${round.name}`)
  const result = await runRound({
    directory,
    lock,
    name: `check ${round.name}`,
    record: { inputs: { environment: before.environment, hash: before.hash }, narrowed: partial },
    steps: round.steps(options, directory),
    // A narrowed run is for reading a bridge's or a mutant's output, such as a dump.
    stream: partial,
  })
  process.stdout.write(
    `${round.name}: ${verdicts[result.status]} in ${result.elapsedSeconds} s; receipt ${result.receipt}\n`,
  )
  return result.status === 'passed'
    ? settle(round, before, result.receipt, partial)
    : result.exitCode
}

/** The options of a run, which only a named round that takes them may narrow. */
function optionsFor(
  round: RoundDefinition | undefined,
  names: readonly string[],
  parsed: Parsed,
): RoundOptions {
  const seeds = parsed.values.seeds as string | undefined
  const options: RoundOptions = {
    batch: parsed.values.batch as string | undefined,
    dump: parsed.values.dump === true,
    features: parsed.values.features === true,
    names,
    seeds: seeds === undefined ? undefined : parseSeeds(seeds),
  }
  if (!narrowed(options)) return options
  if (round?.validate === undefined)
    throw new UsageError(
      'only the lean and mutants rounds take names and narrowing options: name the round, as in ' +
        '`pnpm check lean spec --batch reconcile`',
    )
  round.validate(options)
  return options
}

/** The exit codes of rounds by how much they say: an interrupt, then a failure, a round that
 * could not run, an incomplete one and a pass. */
const SEVERITY = [
  EXIT_CODES.cancelled,
  EXIT_CODES.failed,
  EXIT_CODES.blocked,
  EXIT_CODES.timed_out,
  EXIT_CODES.passed,
]

const mostSevere = (codes: readonly number[]): number =>
  SEVERITY.find((code) => codes.includes(code)) ?? EXIT_CODES.passed

/** Runs the rounds in order and returns the most severe exit code; stops at the first round that
 * does not pass unless `keepGoing` is set, and at an interrupt in any case. */
async function runAll(
  rounds: readonly RoundDefinition[],
  options: RoundOptions,
  fresh: boolean,
  keepGoing: boolean,
): Promise<number> {
  const invocation = ['pnpm check', ...process.argv.slice(3)].join(' ')
  return await withLock(invocation, async (lock) => {
    const codes: number[] = []
    for (const round of rounds) {
      const code = await runOne(round, options, fresh, lock)
      codes.push(code)
      if (interrupted() || (code !== 0 && !keepGoing)) break
    }
    return mostSevere(codes)
  })
}

async function run({ positionals, values }: Parsed): Promise<number> {
  const [name, ...names] = positionals
  const rounds = name === undefined ? ROUNDS : [roundNamed(name)]
  // String options that are not `multiple` parse to strings.
  const options = optionsFor(name === undefined ? undefined : rounds[0], names, {
    positionals,
    values,
  })
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
    'Exit codes: 0 passed, 1 failed, 2 usage error, 3 could not run (nothing was judged), 124 ' +
      'incomplete (out of budget, or its files changed while it ran; rerun the whole round). An ' +
      'interrupt stops the round and ends the command by its signal, 130 for Ctrl-C; a second ' +
      'one stops the steps at once. With --keep-going the most severe code is returned.',
  ],
  examples: [
    'pnpm check                  # every round that has not passed on its current inputs',
    'pnpm check --plan           # what would run, and why',
    'pnpm check lean             # one round',
    'pnpm check lean spec        # one bridge of the gate',
    'pnpm check lean spec --batch reconcile-hazards --seeds 10563 --dump',
    'pnpm check mutants own-node-pins-dropped --seeds 1-200',
  ],
  name: 'check',
  options: {
    'batch': {
      description: 'lean: the one batch of the one bridge named to run.',
      placeholder: '<name>',
      type: 'string',
    },
    'dump': {
      description:
        'lean: show each seed of the bridge named: its case, the reference and the comparison.',
      type: 'boolean',
    },
    'features': {
      description:
        'lean spec: how often each feature occurs among the generated cases; compares nothing.',
      type: 'boolean',
    },
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
      description:
        "lean: the seeds of the bridge named in place of each batch's own; mutants: the seeds " +
        'of each Spec bridge run in place of 1-1500. Seeds and ranges joined by commas.',
      placeholder: '<seeds>',
      type: 'string',
    },
  },
  run,
  sections: [
    { rows: ROUNDS.map((round) => [round.name, round.summary] as const), title: 'Rounds' },
    {
      rows: [
        ['lean <bridge...>', 'Only these bridges of the gate, after the build; no axiom audit.'],
        ['mutants <mutant...>', 'Only these mutants, after the unmutated control run.'],
        ...BRIDGES.filter((bridge) => bridge.batches !== undefined).map(
          (bridge) => [`lean ${bridge.family}`, `--batch ${bridge.batches!.join(', ')}`] as const,
        ),
      ],
      title: 'Narrowed runs, which record no pass',
    },
  ],
  summary: 'Is the change correct? Runs every round that has not passed on its current inputs.',
  usage: '[round [bridge... | mutant...]] [options]',
}
