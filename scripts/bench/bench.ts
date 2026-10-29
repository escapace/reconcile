import { spawnSync } from 'node:child_process'
import { rmSync } from 'node:fs'
import { loadavg } from 'node:os'
import path from 'node:path'
import { UsageError, type Command, type Option, type Parsed } from '../framework/command'
import { script } from '../framework/entry'
import { withLock } from '../framework/lock'
import { ROOT } from '../framework/paths'
import { runRound, stampedDirectory, type Step } from '../framework/round'
import { EXPORTS } from '../bundles'
import {
  completeExperiment,
  createExperiment,
  EXPERIMENTS,
  resolveControl,
  resolveExperiment,
  type Control,
} from './experiments'
import { report } from './report'
import { SCENARIOS, selectScenarios, SETS } from './scenarios'

const TREE: Option = {
  description: 'The source tree to measure; by default this checkout.',
  placeholder: '<dir>',
  type: 'string',
}
const CONTROL: Option = {
  description:
    'The control to compare with: an experiment, by its name, its directory or `latest`, which ' +
    'keeps the round, or any source tree.',
  placeholder: '<control>',
  type: 'string',
}
const SIZE: Option = {
  default: '256',
  description: "The diagnostics' size; most scale with it.",
  placeholder: '<n>',
  type: 'string',
}
const BATCHES: Option = {
  default: '200',
  description: 'Measured batches.',
  placeholder: '<n>',
  type: 'string',
}
const WARMUP: Option = {
  default: '5',
  description: 'Warmup batches before measurement.',
  placeholder: '<n>',
  type: 'string',
}

const OUT = { '--out': 'output is kept in the round directory the command prints' }

/** The value of a string option. */
const text = (parsed: Parsed, name: string): string | undefined =>
  parsed.values[name] as string | undefined

/** An integer option, at least `minimum`. */
function integer(parsed: Parsed, name: string, minimum: number): number {
  const value = Number(text(parsed, name))
  if (!Number.isSafeInteger(value) || value < minimum)
    throw new UsageError(
      `--${name} takes an integer of at least ${minimum}, not "${text(parsed, name)}"`,
    )
  return value
}

const treeOf = (parsed: Parsed): string => path.resolve(ROOT, text(parsed, 'tree') ?? '.')

const controlOf = (parsed: Parsed): Control | undefined => {
  const value = text(parsed, 'control')
  return value === undefined ? undefined : resolveControl(value)
}

/** Warns when other work on the machine would move the measurements. */
function warnLoad(): void {
  const [load] = loadavg()
  if (load > 1)
    console.warn(`Warning: the load average is ${load.toFixed(2)}; other work moves measurements.`)
}

/** Runs the steps as one round under the lock, their output shown as it runs, and keeps the
 * round under `rounds`, an experiment's, when there is one. */
async function measure(
  name: string,
  rounds: string | undefined,
  steps: (directory: string) => Step[],
): Promise<number> {
  warnLoad()
  const invocation = ['pnpm bench', ...process.argv.slice(3)].join(' ')
  return await withLock(invocation, async (lock) => {
    const directory =
      rounds === undefined ? stampedDirectory(`bench-${name}`) : stampedDirectory(name, rounds)
    const result = await runRound({
      directory,
      lock,
      name: `bench ${name}`,
      steps: steps(directory),
      stream: true,
    })
    console.log(`\n${name}: ${result.status}; output and receipt in ${directory}`)
    return result.exitCode
  })
}

const tool = (name: string, config: object): Step => ({
  command: script(`scripts/bench/${name}.ts`, config),
  name,
})

/** The commit `revision` names; anything else is a usage error. */
function commitOf(revision: string): string {
  const commit = spawnSync('git', ['rev-parse', '--verify', '--quiet', `${revision}^{commit}`], {
    cwd: ROOT,
    encoding: 'utf8',
  })
  if (commit.status !== 0) throw new UsageError(`no revision "${revision}"`)
  return commit.stdout.trim()
}

/** What to try once an experiment exists. */
const nextSteps = (name: string, tree: string, built: boolean): string =>
  [
    `\nExperiment ${name}; its control is ${tree}. Next:`,
    `  pnpm bench profile <scenario> --tree ${tree}   where the control spends its time`,
    `  pnpm bench counts <scenario> --control ${name}   after a change: the counters that moved`,
    `  pnpm bench ab default --control ${name}   then small, then <scenario> --decide twice`,
    `  pnpm build && pnpm bench size --control ${name}${built ? '' : '   (after pnpm bench control --build)'}`,
    `  pnpm bench report ${name}`,
  ].join('\n')

const control: Command = {
  description: [
    'The control is exported with `git archive`, or copied with --worktree, into the ' +
      `experiment's \`tree/\` under ${EXPERIMENTS}. It runs and builds with this checkout's ` +
      'dependencies, as the measured tree does.',
  ],
  examples: ['pnpm bench control', 'pnpm bench control trunk --build'],
  name: 'control',
  options: {
    build: {
      description: 'Also build the control, which comparing bundle sizes needs.',
      type: 'boolean',
    },
    worktree: {
      description: 'Freeze the working tree with its uncommitted changes instead of a revision.',
      type: 'boolean',
    },
  },
  summary: 'Freeze a control and start an experiment against it.',
  usage: '[<revision>] [options]',
  async run(parsed) {
    const worktree = parsed.values.worktree === true
    const build = parsed.values.build === true
    if (parsed.positionals.length > 1 || (worktree && parsed.positionals.length > 0))
      throw new UsageError('control takes one revision, or --worktree')
    const commit = commitOf(parsed.positionals[0] ?? 'HEAD')
    const directory = createExperiment(`${commit.slice(0, 7)}${worktree ? '-worktree' : ''}`)
    const tree = path.join(directory, 'tree')
    const code = await measure('control', path.join(directory, 'rounds'), () => [
      tool('control', { build, commit, directory, worktree }),
      ...(build
        ? [{ command: ['pnpm', 'run', '--silent', 'build'], cwd: tree, name: 'build' }]
        : []),
    ])
    if (code !== 0) {
      rmSync(directory, { force: true, recursive: true })
      console.log('The control was not frozen, so its experiment was removed.')
      return code
    }
    completeExperiment(directory, { commit, created: new Date().toISOString(), worktree })
    console.log(nextSteps(path.basename(directory), tree, build))
    return 0
  },
}

const MODES = ['cpu', 'heap', 'deopt']

/** The sampling interval: the option's, or the mode's default. */
const intervalOf = (parsed: Parsed, mode: string): number =>
  text(parsed, 'interval') === undefined
    ? mode === 'heap'
      ? 32_768
      : 1000
    : integer(parsed, 'interval', 1)

const profile: Command = {
  examples: ['pnpm bench profile reconcile', 'pnpm bench profile diag-map-update --mode heap'],
  name: 'profile',
  options: {
    batches: BATCHES,
    interval: {
      description:
        'The sampling interval: microseconds for cpu (default 1000), bytes for heap (default 32768).',
      placeholder: '<n>',
      type: 'string',
    },
    mode: {
      default: 'cpu',
      description: 'cpu or heap samples and attributes to source; deopt traces V8.',
      placeholder: '<mode>',
      type: 'string',
    },
    size: SIZE,
    tree: TREE,
    warmup: WARMUP,
  },
  retired: {
    ...OUT,
    '--baseline': 'compare counters with `pnpm bench counts <scenario> --control <control>`',
    '--bundle-only': 'bundles are built by the command that runs them',
    '--candidate': 'use --tree',
    '--cpu-interval': 'use --interval',
    '--heap-interval': 'use --interval',
  },
  summary: 'Where does the time or the allocation go?',
  usage: '<scenario> [options]',
  async run(parsed) {
    const scenarios = selectScenarios(parsed.positionals)
    if (scenarios.length !== 1 || parsed.positionals.length !== 1)
      throw new UsageError('profile takes one scenario')
    const mode = text(parsed, 'mode') ?? 'cpu'
    if (mode === 'counts')
      throw new UsageError('counts have a command of their own: pnpm bench counts <scenario>')
    if (!MODES.includes(mode))
      throw new UsageError(`--mode takes cpu, heap or deopt, not "${mode}"`)
    const config = {
      batches: integer(parsed, 'batches', 1),
      interval: intervalOf(parsed, mode),
      mode,
      scenario: scenarios[0],
      size: integer(parsed, 'size', 1),
      tree: treeOf(parsed),
      warmup: integer(parsed, 'warmup', 0),
    }
    return await measure('profile', undefined, (directory) => [
      tool('profile', { ...config, directory }),
    ])
  },
}

const counts: Command = {
  examples: ['pnpm bench counts reconcile', 'pnpm bench counts small --control latest'],
  name: 'counts',
  options: { batches: BATCHES, control: CONTROL, size: SIZE, tree: TREE, warmup: WARMUP },
  retired: { ...OUT, '--baseline': 'use --control <control>', '--candidate': 'use --tree' },
  summary:
    'Which events, such as reads and constructions, does a scenario make, and which changed?',
  usage: '<scenario...> [options]',
  async run(parsed) {
    const scenarios = selectScenarios(parsed.positionals)
    if (scenarios.length === 0) throw new UsageError('counts takes at least one scenario')
    const against = controlOf(parsed)
    const config = {
      batches: integer(parsed, 'batches', 1),
      control: against?.tree,
      scenarios,
      size: integer(parsed, 'size', 1),
      tree: treeOf(parsed),
      warmup: integer(parsed, 'warmup', 0),
    }
    return await measure('counts', against?.rounds, (directory) => [
      tool('counts', { ...config, directory }),
    ])
  },
}

/**
 * The protocol rule an A/B round serves: a deciding round has at least 32 pairs of a second or
 * more each; a default or small round is its set with at least 10 pairs. Any other round is
 * custom, and `ab` marks a round whose trees hold the same sources as an A/A round.
 */
function kindOf(names: readonly string[], decide: boolean, pairs: number, seconds: number): string {
  if (decide) return pairs >= 32 && seconds >= 1 ? 'deciding' : 'custom'
  const set = names.length === 0 ? 'default' : names.length === 1 ? names[0] : ''
  return Object.hasOwn(SETS, set) && pairs >= 10 ? set : 'custom'
}

/** An option of `ab` that takes a count or `auto`. */
const automatic = (parsed: Parsed, name: string, minimum: number): number | 'auto' =>
  text(parsed, name) === 'auto' ? 'auto' : integer(parsed, name, minimum)

const ab: Command = {
  examples: [
    'pnpm bench ab default --control latest',
    'pnpm bench ab small --control latest',
    'pnpm bench ab reconcile --decide --control latest',
  ],
  name: 'ab',
  options: {
    batches: {
      default: 'auto',
      description: 'Batches per process, or auto for about --seconds of measured work.',
      placeholder: '<n>',
      type: 'string',
    },
    control: CONTROL,
    decide: {
      description: 'A deciding round: 32 pairs of 1 second each, unless set.',
      type: 'boolean',
    },
    pairs: {
      description: 'Pairs of processes, an even count: 10, or 32 with --decide.',
      placeholder: '<n>',
      type: 'string',
    },
    seconds: {
      description: 'Measured seconds per process when --batches is auto: 0.5, or 1 with --decide.',
      placeholder: '<s>',
      type: 'string',
    },
    size: SIZE,
    tree: TREE,
    warmup: {
      default: 'auto',
      description: 'Warmup batches, or auto for half the batches.',
      placeholder: '<n>',
      type: 'string',
    },
  },
  retired: {
    ...OUT,
    '--baseline': 'use --control <control>',
    '--candidate': 'use --tree',
    '--round': 'name the set as an argument: pnpm bench ab small',
    '--scenario': 'name scenarios as arguments: pnpm bench ab <scenario...>',
  },
  summary: 'Is it faster? Alternating fresh-process pairs against the control.',
  usage: '[default | small | <scenario>...] --control <control> [options]',
  async run(parsed) {
    const against = controlOf(parsed)
    if (against === undefined)
      throw new UsageError(
        'ab needs --control <control>; start an experiment with `pnpm bench control`',
      )
    const decide = parsed.values.decide === true
    const pairs =
      text(parsed, 'pairs') === undefined ? (decide ? 32 : 10) : integer(parsed, 'pairs', 2)
    if (pairs % 2 !== 0)
      throw new UsageError('--pairs takes an even count, so each order runs equally')
    const seconds = Number(text(parsed, 'seconds') ?? (decide ? 1 : 0.5))
    if (!(seconds > 0)) throw new UsageError('--seconds takes a positive number')
    const config = {
      batches: automatic(parsed, 'batches', 1),
      control: against.tree,
      kind: kindOf(parsed.positionals, decide, pairs, seconds),
      pairs,
      scenarios: selectScenarios(
        parsed.positionals.length === 0 ? ['default'] : parsed.positionals,
      ),
      seconds,
      size: integer(parsed, 'size', 1),
      tree: treeOf(parsed),
      warmup: automatic(parsed, 'warmup', 0),
    }
    return await measure('ab', against.rounds, (directory) => [
      tool('ab', { ...config, directory }),
    ])
  },
}

const size: Command = {
  description: [
    'The trees must be built: `pnpm build` builds this checkout, and `pnpm bench control ' +
      "--build` an experiment's control. --modules builds from the sources instead.",
  ],
  examples: [
    'pnpm build && pnpm bench size --control latest',
    'pnpm bench size --modules reconcile --control latest',
  ],
  name: 'size',
  options: {
    control: CONTROL,
    modules: {
      description: `The bytes each source module adds to one bundle: exports joined by +, of ${EXPORTS.join(', ')}.`,
      placeholder: '<exports>',
      type: 'string',
    },
    tree: TREE,
  },
  retired: {
    ...OUT,
    '--compare': 'use --control <control>',
    '--entry': 'use --tree <dir>, whose built package is measured',
    '--no-smoke': '`pnpm check lib` runs the smoke tests',
  },
  summary: 'How large are the consumer bundles, and which modules make them so?',
  usage: '[options]',
  async run(parsed) {
    const against = controlOf(parsed)
    const modules = text(parsed, 'modules')?.split('+')
    const unknown = modules?.filter((name) => !EXPORTS.includes(name)) ?? []
    if (unknown.length > 0)
      throw new UsageError(
        `--modules takes exports of ${EXPORTS.join(', ')}, not ${unknown.join(', ')}`,
      )
    const config = { control: against?.tree, modules, tree: treeOf(parsed) }
    return await measure('size', against?.rounds, (directory) => [
      tool('size', { ...config, directory }),
    ])
  },
}

const reportCommand: Command = {
  examples: ['pnpm bench report', 'pnpm bench report <experiment>'],
  name: 'report',
  summary: "What do an experiment's rounds conclude, and which are missing?",
  usage: '[<experiment>]',
  async run(parsed) {
    if (parsed.positionals.length > 1) throw new UsageError('report takes one experiment')
    console.log(report(resolveExperiment(parsed.positionals[0] ?? 'latest')))
    return await Promise.resolve(0)
  },
}

export const bench: Command = {
  commands: [control, profile, counts, ab, size, reportCommand],
  description: [
    `Scenarios: ${SCENARIOS.join(', ')}. \`ab\` and \`counts\` also take the sets ${Object.keys(SETS).join(' and ')}.`,
    '--tree is the source tree measured, this checkout by default. --control is the control to ' +
      'compare with: an experiment, which also keeps the round, or any source tree. Each ' +
      'command but `report` runs as one round within the 295-second budget and holds the lock ' +
      'that `pnpm check` takes.',
  ],
  examples: ['pnpm bench control', 'pnpm bench ab default --control latest', 'pnpm bench report'],
  name: 'bench',
  summary: 'Is it faster or smaller? Measures against a frozen control, one round at a time.',
  usage: '<command> [options]',
}
