/**
 * `pnpm bench`: one entry point for every benchmark and measurement. Each command answers one
 * question and runs as one round within the 295-second budget, including shutdown of child
 * processes. `pnpm bench help` lists the commands.
 */

import { spawnSync } from 'node:child_process'
import { mkdtempSync } from 'node:fs'
import { tmpdir } from 'node:os'
import path from 'node:path'
import { expandRound, rounds, scenarioNames } from './bench-workloads'

const ROOT = path.resolve(import.meta.dirname, '..')

const usage = `Usage:
  pnpm bench ab --baseline <tree> ...       Is it faster? (fresh-process pairs; decides)
  pnpm bench profile <scenario> ...         Where does the work or time go?
  pnpm bench size [--compare sizes.json]    How large are the consumer bundles?

Scenarios: ${scenarioNames.join(', ')}.
\`ab\` takes \`--round default\` (the first six; the default) or \`--round small\` (the ten on 1
and 16 keys) in place of \`--scenario\`. \`profile\` and \`ab\` also take the diag-* diagnostics
that \`pnpm bench profile --help\` lists.`

const tsx = (script: string) => (arguments_: string[]) => [
  'pnpm',
  'exec',
  'tsx',
  script,
  ...arguments_,
]

/** The command line of each subcommand; `ab` defaults to the default round. */
const commands: Record<string, (arguments_: string[]) => string[]> = {
  profile: tsx('scripts/profile.ts'),
  size: tsx('scripts/bundle-size.ts'),
  ab: (arguments_) => [
    'python3',
    'scripts/ab-time.py',
    ...(arguments_.some(
      (argument) => argument === '--scenario' || argument.startsWith('--scenario='),
    )
      ? arguments_
      : [...arguments_, ...rounds.default.flatMap((name) => ['--scenario', name])]),
  ],
}

const [name, ...arguments_] = process.argv.slice(2)
if (name === undefined || name === 'help' || name === '-h' || name === '--help') {
  console.log(usage)
  process.exit(0)
}
const command = commands[name]
if (command === undefined) {
  console.error(`Unknown command ${name}.\n\n${usage}`)
  process.exit(2)
}
let line: string[]
try {
  line = command(expandRound(arguments_))
} catch (error) {
  console.error((error as Error).message)
  process.exit(2)
}
// Help exits before any measurement, so it runs without a budget or a receipt.
if (arguments_.includes('--help') || arguments_.includes('-h')) {
  process.exit(spawnSync(line[0], line.slice(1), { cwd: ROOT, stdio: 'inherit' }).status ?? 1)
}
const receipt = path.join(mkdtempSync(path.join(tmpdir(), 'reconcile-bench-')), 'receipt.json')
const result = spawnSync(
  'python3',
  ['scripts/bounded-check.py', '--seconds', '295', '--receipt', receipt, '--', ...line],
  { cwd: ROOT, stdio: 'inherit' },
)
console.log(`Receipt: ${receipt}`)
process.exit(result.status ?? 1)
