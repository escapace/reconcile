import { spawnSync } from 'node:child_process'
import { existsSync } from 'node:fs'
import { homedir } from 'node:os'
import path from 'node:path'
import { ROOT } from '../framework/paths'
import type { Step } from '../framework/round'

/** What a round may be narrowed to: some mutants, or another seed count. A narrowed run records
 * no pass. */
export interface RoundOptions {
  readonly names: readonly string[]
  readonly seeds: string | undefined
}

/** One round of `pnpm check`: a complete validation that answers one question within one
 * budget. */
export interface RoundDefinition {
  readonly name: string
  readonly summary: string
  /** Files that cannot change the round's result; every other file of the working tree, tracked
   * or untracked, is an input. */
  readonly exclude: readonly string[]
  /** Whether a run with these options is narrower than the round, and so records no pass. */
  readonly narrowed: (options: RoundOptions) => boolean
  /** The round's commands; `directory` holds its logs, receipt and anything else it writes. */
  readonly steps: (options: RoundOptions, directory: string) => Step[]
  /** Tracked files the round itself may rewrite, such as the README that the build regenerates. */
  readonly outputs?: readonly string[]
}

/** The Lean sources and toolchain, which only the Lean rounds read. */
const LEAN = ['*.lean', 'lake-manifest.json', 'lakefile.toml', 'lean-toolchain', 'lean/fixtures/']
/** The guides, which no round but `static` reads. */
const GUIDES = ['AGENTS.md', 'docs/']
/** The README and the guides. Only `static` reads them, and `lib` the README, whose API section
 * the build regenerates. */
const DOCS = ['README.md', ...GUIDES]
/** The measurement tooling, which only `static` and `test` read. */
const BENCH = [
  'perf/',
  'scripts/ab-time.py',
  'scripts/bench/',
  'scripts/profile-attribution.ts',
  'scripts/profile-counts.ts',
  'scripts/profile-deopts.ts',
  'scripts/profile-frames.ts',
  'scripts/profile-summary.ts',
  'scripts/profile.ts',
  'scripts/test-ab-time.py',
]
/** What `lib` reads of the measurement tooling besides: the workloads and diagnostics, which
 * `profile-scenarios.spec.ts` runs against the package, and the bundle checks. */
const LIB_TOOLING = [
  'scripts/bench-workloads.ts',
  'scripts/bundle-size.ts',
  'scripts/profile-scenarios.ts',
]

/** The specs that run only with a native `Temporal`. */
const TEMPORAL_SPECS = ['src/__tests__/deserialize-limit.spec.ts', 'src/__tests__/temporal.spec.ts']

const pnpm = (name: string, ...arguments_: string[]): Step => ({
  command: ['pnpm', ...arguments_],
  name,
})

/** A TypeScript entry point run by Node with tsx's loader, and Node's own flags first. */
const tsx = (
  name: string,
  file: string,
  arguments_: string[] = [],
  flags: string[] = [],
): Step => ({
  command: [process.execPath, ...flags, '--import', 'tsx', file, ...arguments_],
  name,
})

/** `PATH` with elan's default install directory, where the Lean toolchain lives, if it is
 * missing. */
function withElan(PATH: string): string {
  const elan = path.join(homedir(), '.elan', 'bin')
  return existsSync(elan) && !PATH.split(path.delimiter).includes(elan)
    ? `${elan}${path.delimiter}${PATH}`
    : PATH
}

/** The environment of the Lean steps: the toolchain on PATH, the C compiler that skips
 * optimizing the oracle's imported dependencies, and no artifact cache, whose objects were built
 * with other settings. A round resolves it once, when its first Lean step starts. */
function leanEnvironment(): () => Record<string, string> {
  let environment: Record<string, string> | undefined
  return () => {
    if (environment !== undefined) return environment
    const PATH = withElan(process.env.PATH ?? '')
    const prefix = spawnSync('lean', ['--print-prefix'], {
      encoding: 'utf8',
      env: { ...process.env, PATH },
      timeout: 30_000,
    })
    if (prefix.status !== 0) throw new Error(`lean --print-prefix failed: ${prefix.stderr}`)
    environment = {
      LAKE_ARTIFACT_CACHE: 'false',
      LEAN_CC: path.join(ROOT, 'scripts', 'lean-cc.py'),
      LEAN_SYSROOT: prefix.stdout.trim(),
      PATH,
    }
    return environment
  }
}

/** The first Lean step: elan installs the version `lean-toolchain` names, if it lacks it, within
 * the round's budget. */
const toolchain = (): Step => ({
  command: ['lean', '--version'],
  env: { PATH: withElan(process.env.PATH ?? '') },
  name: 'lean toolchain',
})

/** Builds the proofs and the oracle with warnings as errors. */
const lakeBuild = (environment: () => Record<string, string>): Step => ({
  command: ['lake', 'build', '--wfail'],
  env: environment,
  name: 'lake build',
})

const whole = (): boolean => false

/** Every round, in the order `pnpm check` runs them: the fastest feedback first. */
export const ROUNDS: readonly RoundDefinition[] = [
  {
    exclude: ['*.lean'],
    name: 'static',
    narrowed: whole,
    summary: 'Types, ESLint and file names.',
    steps: () => [
      pnpm('typecheck', 'run', '--silent', 'typecheck'),
      pnpm('ls-lint', 'run', '--silent', 'ls-lint'),
      pnpm('eslint', 'exec', 'eslint', '--concurrency', 'auto'),
    ],
  },
  {
    exclude: [...LEAN, ...DOCS],
    name: 'test',
    narrowed: whole,
    summary: 'Every spec in the neutral and poisoned projects, then fallow on their coverage.',
    steps: () => [
      pnpm('vitest', 'run', '--silent', 'test'),
      // fallow's CRAP score reads the coverage the tests just wrote.
      pnpm('fallow', 'exec', 'fallow', '--fail-on-issues'),
    ],
  },
  {
    exclude: [...LEAN, ...GUIDES, ...BENCH],
    name: 'lib',
    narrowed: whole,
    outputs: ['README.md'],
    summary: 'The built package: its build, the specs against it and every per-export bundle.',
    steps: (_, directory) => [
      pnpm('build', 'run', '--silent', 'build'),
      pnpm('vitest', 'exec', 'vitest', '--no-watch', '--config', 'vitest-library.config.ts'),
      tsx('bundles', 'scripts/bundle-size.ts', ['--out', path.join(directory, 'bundles')]),
    ],
  },
  {
    exclude: [...DOCS, ...BENCH, ...LIB_TOOLING],
    name: 'temporal',
    narrowed: whole,
    summary:
      "The cases that need Node's native Temporal, on the sources, the package and the bridges.",
    steps: () => {
      const environment = leanEnvironment()
      const specs = (name: string, config: string): Step =>
        pnpm(
          name,
          'exec',
          'vitest',
          'run',
          '--config',
          config,
          ...TEMPORAL_SPECS,
          '--execArgv=--harmony-temporal',
        )
      return [
        specs('sources', 'vitest.config.neutral.ts'),
        pnpm('build', 'run', '--silent', 'build'),
        specs('package', 'vitest-library.config.ts'),
        toolchain(),
        lakeBuild(environment),
        {
          ...tsx('bridges', 'scripts/check-lean.ts', [], ['--harmony-temporal']),
          env: environment,
        },
      ]
    },
  },
  {
    exclude: [...DOCS, ...BENCH, ...LIB_TOOLING],
    name: 'lean',
    narrowed: whole,
    summary: 'The gate: proofs without warnings or extra axioms, and every runtime-to-Lean bridge.',
    steps: () => {
      const environment = leanEnvironment()
      return [
        toolchain(),
        lakeBuild(environment),
        { command: ['python3', 'scripts/check-axioms.py'], env: environment, name: 'axiom audit' },
        {
          command: ['python3', 'scripts/test-axioms.py'],
          name: 'axiom audit self-test',
          env: () => ({ ...environment(), PYTHONDONTWRITEBYTECODE: '1' }),
        },
        { ...tsx('bridges', 'scripts/check-lean.ts'), env: environment },
      ]
    },
  },
  {
    exclude: [...DOCS, ...BENCH, ...LIB_TOOLING],
    name: 'mutants',
    summary: 'The mutation audit: every deliberate runtime defect the bridges must detect.',
    narrowed: ({ names, seeds }) => names.length > 0 || (seeds !== undefined && seeds !== '1500'),
    steps: ({ names, seeds }) => [
      toolchain(),
      lakeBuild(leanEnvironment()),
      tsx('audit', 'scripts/check/mutants.ts', ['--seeds', seeds ?? '1500', ...names]),
    ],
  },
]
