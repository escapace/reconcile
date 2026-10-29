import { spawnSync } from 'node:child_process'
import { expandRound, rounds, scenarioNames } from '../bench-workloads'
import { UsageError, type Command } from '../framework/command'
import { withLock } from '../framework/lock'
import { ROOT } from '../framework/paths'
import { runRound } from '../framework/round'

const tsx = (file: string) => (arguments_: readonly string[]) => [
  process.execPath,
  '--import',
  'tsx',
  file,
  ...arguments_,
]

/** The tool's command line, with `--round` expanded to the scenarios it names. */
function commandLine(
  line: (arguments_: readonly string[]) => readonly string[],
  arguments_: readonly string[],
): readonly string[] {
  try {
    return line(expandRound([...arguments_]))
  } catch (error) {
    throw new UsageError((error as Error).message)
  }
}

/** Runs a tool as one round under the lock, its output shown as it runs. */
async function measure(
  name: string,
  command: readonly string[],
  arguments_: readonly string[],
): Promise<number> {
  return await withLock(['pnpm bench', name, ...arguments_].join(' '), async (lock) => {
    const result = await runRound({
      lock,
      name: `bench ${name}`,
      steps: [{ command, name }],
      stream: true,
    })
    console.log(`Receipt: ${result.receipt}`)
    return result.exitCode
  })
}

/** A measurement tool that parses its own arguments. */
function tool(
  name: string,
  summary: string,
  usage: string,
  line: (arguments_: readonly string[]) => readonly string[],
): Command {
  return {
    name,
    passthrough: true,
    summary,
    usage,
    async run({ positionals: arguments_ }) {
      const command = commandLine(line, arguments_)
      // Help exits before any measurement, so it runs without a budget or a lock.
      if (!arguments_.includes('--help') && !arguments_.includes('-h'))
        return await measure(name, command, arguments_)
      return spawnSync(command[0], command.slice(1), { cwd: ROOT, stdio: 'inherit' }).status ?? 1
    },
  }
}

export const bench: Command = {
  commands: [
    tool(
      'ab',
      'Is it faster? Fresh-process pairs against a control; decides.',
      '--baseline <tree> [--round default|small | --scenario <name>...] [options]',
      (arguments_) => [
        'python3',
        'scripts/ab-time.py',
        ...(arguments_.some(
          (argument) => argument === '--scenario' || argument.startsWith('--scenario='),
        )
          ? arguments_
          : [...arguments_, ...rounds.default.flatMap((scenario) => ['--scenario', scenario])]),
      ],
    ),
    tool(
      'profile',
      'Where does the work or time go?',
      '<scenario> [options]',
      tsx('scripts/profile.ts'),
    ),
    tool(
      'size',
      'How large are the consumer bundles?',
      '[--compare sizes.json] [options]',
      tsx('scripts/bundle-size.ts'),
    ),
  ],
  description: [
    `Scenarios: ${scenarioNames.join(', ')}. \`ab\` takes \`--round default\` (the first six; ` +
      'the default) or `--round small` (the ten on 1 and 16 keys) in place of `--scenario`. ' +
      '`profile` and `ab` also take the diag-* diagnostics that `pnpm bench profile --help` lists. ' +
      'Each command runs as one round within the 295-second budget and holds the round lock.',
  ],
  examples: [
    'pnpm bench ab --baseline <control> --out <dir>',
    'pnpm bench profile diag-map-update --mode counts --baseline <control>',
    'pnpm bench size --compare <dir>/sizes.json',
  ],
  name: 'bench',
  summary: 'Is it faster or smaller? Measures against a control, one round at a time.',
  usage: '<command> [options]',
}
