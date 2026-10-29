import { existsSync } from 'node:fs'
import { homedir } from 'node:os'
import path from 'node:path'
import { script } from '../framework/entry'
import { ROOT } from '../framework/paths'
import type { Step } from '../framework/round'
import { UsageError } from '../framework/command'
import { BRIDGES, type Bridge, type Flag } from './bridges'
import { mutantNames } from './mutants'

/** What a run may narrow its round to: some bridges or mutants, one batch, other seeds, a dump
 * or the features report. A narrowed run records no pass. */
export interface RoundOptions {
  readonly batch: string | undefined
  readonly dump: boolean
  readonly features: boolean
  readonly names: readonly string[]
  readonly seeds: readonly number[] | undefined
}

/** Whether a run narrows its round. */
export const narrowed = ({ batch, dump, features, names, seeds }: RoundOptions): boolean =>
  names.length > 0 || batch !== undefined || seeds !== undefined || dump || features

/** One round of `pnpm check`: a complete validation that answers one question within one
 * budget. */
export interface RoundDefinition {
  readonly name: string
  readonly summary: string
  /** Files that cannot change the round's result; every other file of the working tree, tracked
   * or untracked, is an input. */
  readonly exclude: readonly string[]
  /** The round's commands; `directory` holds its logs, receipt and anything else it writes. */
  readonly steps: (options: RoundOptions, directory: string) => Step[]
  /** Tracked files the round itself may rewrite, such as the README that the build regenerates. */
  readonly outputs?: readonly string[]
  /** Raises a usage error for narrowing options the round does not take; a round without it
   * takes none. */
  readonly validate?: (options: RoundOptions) => void
}

/** The Lean sources and toolchain, which only the Lean rounds read. */
const LEAN = ['*.lean', 'lake-manifest.json', 'lakefile.toml', 'lean-toolchain', 'lean/fixtures/']
/** The guides, which no round but `static` reads. */
const GUIDES = ['AGENTS.md', 'docs/']
/** The README and the guides. Only `static` reads them, and `lib` the README, whose API section
 * the build regenerates. */
const DOCS = ['README.md', ...GUIDES]
/** The measurement tooling and the frozen workloads, which `temporal`, `lean` and `mutants` never
 * read. */
const BENCH = ['perf/', 'scripts/bench/', 'scripts/bench-workloads.ts']

/** The specs that run only with a native `Temporal`. */
const TEMPORAL_SPECS = ['src/__tests__/deserialize-limit.spec.ts', 'src/__tests__/temporal.spec.ts']

const pnpm = (name: string, ...arguments_: string[]): Step => ({
  command: ['pnpm', ...arguments_],
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
 * with other settings. */
const leanEnvironment = (): Record<string, string> => ({
  LAKE_ARTIFACT_CACHE: 'false',
  LEAN_CC: path.join(ROOT, 'scripts', 'check', 'cc.sh'),
  PATH: withElan(process.env.PATH ?? ''),
})

/** The first Lean step: elan installs the version `lean-toolchain` names, if it lacks it, within
 * the round's budget. */
const toolchain = (): Step => ({
  command: ['lean', '--version'],
  env: leanEnvironment(),
  name: 'lean toolchain',
})

/** Builds the proofs and the oracle with warnings as errors. */
const lakeBuild = (): Step => ({
  command: ['lake', 'build', '--wfail'],
  env: leanEnvironment(),
  name: 'lake build',
})

const listed = (names: readonly string[]): string => names.join(', ')

/** The bridge a narrowing option applies to: the one bridge named, which must have batches. */
function batchedBridge(names: readonly string[]): { readonly batches: readonly string[] } & Bridge {
  const bridge =
    names.length === 1 ? BRIDGES.find((candidate) => candidate.family === names[0]) : undefined
  if (bridge?.batches === undefined)
    throw new UsageError(
      '--batch, --seeds, --dump and --features narrow one bridge that has batches: ' +
        listed(
          BRIDGES.filter((candidate) => candidate.batches !== undefined).map(
            (candidate) => candidate.family,
          ),
        ),
    )
  return { ...bridge, batches: bridge.batches }
}

/** The flags a run gives that only some bridges with batches take. */
const flagsGiven = ({ dump, features, seeds }: RoundOptions): Flag[] => [
  ...(seeds === undefined ? [] : (['--seeds'] as const)),
  ...(dump ? (['--dump'] as const) : []),
  ...(features ? (['--features'] as const) : []),
]

/** The narrowing options of a run of the `lean` round: bridges, and for one bridge with batches,
 * the batch, the seeds, a dump or the features report it takes. */
function validateLean(options: RoundOptions): void {
  const { batch, dump, names, seeds } = options
  const unknown = names.filter((name) => !BRIDGES.some((bridge) => bridge.family === name))
  if (unknown.length > 0)
    throw new UsageError(
      `unknown bridges: ${listed(unknown)}; the bridges are ${listed(BRIDGES.map((bridge) => bridge.family))}`,
    )
  const flags = flagsGiven(options)
  if (batch === undefined && flags.length === 0) return
  const { batches, family, takes = [] } = batchedBridge(names)
  if (batch !== undefined && !batches.includes(batch))
    throw new UsageError(`${family} has no batch "${batch}"; its batches are ${listed(batches)}`)
  const refused = flags.filter((flag) => !takes.includes(flag))
  if (refused.length > 0) throw new UsageError(`${family} takes no ${listed(refused)}`)
  if (dump && seeds === undefined) throw new UsageError('--dump needs --seeds, the seeds to show')
}

/** The narrowing options of a run of the `mutants` round: mutants and seeds. */
function validateMutants({ batch, dump, features, names }: RoundOptions): void {
  const unknown = names.filter((name) => !mutantNames.includes(name))
  if (unknown.length > 0)
    throw new UsageError(
      `unknown mutants: ${listed(unknown)}; the mutants are ${listed(mutantNames)}`,
    )
  if (batch !== undefined || dump || features)
    throw new UsageError('the mutants round takes mutant names and --seeds only')
}

/** The seeds of each Spec bridge run of the mutation audit, unless a run names others. */
const AUDIT_SEEDS = Array.from({ length: 1500 }, (_, index) => index + 1)

/** Every round, in the order `pnpm check` runs them: the fastest feedback first. */
export const ROUNDS: readonly RoundDefinition[] = [
  {
    exclude: ['*.lean'],
    name: 'static',
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
    summary: 'Every spec in the neutral and poisoned projects, then fallow on their coverage.',
    steps: () => [
      pnpm('vitest', 'run', '--silent', 'test'),
      // fallow's CRAP score reads the coverage the tests just wrote.
      pnpm('fallow', 'exec', 'fallow', '--fail-on-issues'),
    ],
  },
  {
    // The library suite runs the diagnostics, so `lib` reads the workloads they build on.
    exclude: [...LEAN, ...GUIDES, 'perf/'],
    name: 'lib',
    outputs: ['README.md'],
    summary: 'The built package: its build, the specs against it and every per-export bundle.',
    steps: (_, directory) => [
      pnpm('build', 'run', '--silent', 'build'),
      pnpm('vitest', 'exec', 'vitest', '--no-watch', '--config', 'vitest-library.config.ts'),
      {
        command: script('scripts/bundles.ts', { directory: path.join(directory, 'bundles') }),
        name: 'bundles',
      },
    ],
  },
  {
    exclude: [...DOCS, ...BENCH, 'scripts/bundles.ts'],
    name: 'temporal',
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
        lakeBuild(),
        {
          command: script('scripts/check/lean.ts', { families: [] }, ['--harmony-temporal']),
          env: environment,
          name: 'bridges',
        },
      ]
    },
  },
  {
    exclude: [...DOCS, ...BENCH, 'scripts/bundles.ts'],
    name: 'lean',
    summary: 'The gate: proofs without warnings or extra axioms, and every runtime-to-Lean bridge.',
    validate: validateLean,
    steps: (options, directory) => {
      const environment = leanEnvironment()
      const { batch, dump, features, names: families, seeds } = options
      const bridges = {
        command: script('scripts/check/lean.ts', { batch, dump, families, features, seeds }),
        env: environment,
        name: 'bridges',
      }
      // A narrowed run is for one bridge's failures; the proofs need no audit for it.
      if (narrowed(options)) return [toolchain(), lakeBuild(), bridges]
      return [
        toolchain(),
        lakeBuild(),
        {
          command: script('scripts/check/axioms.ts', { directory }),
          env: environment,
          name: 'axiom audit',
        },
        {
          command: script('scripts/check/axioms.ts', { control: true, directory }),
          env: environment,
          name: 'axiom audit control',
        },
        bridges,
      ]
    },
  },
  {
    exclude: [...DOCS, ...BENCH, 'scripts/bundles.ts'],
    name: 'mutants',
    summary: 'The mutation audit: every deliberate runtime defect the bridges must detect.',
    validate: validateMutants,
    steps: ({ names, seeds }) => [
      toolchain(),
      lakeBuild(),
      {
        command: script('scripts/check/mutants.ts', { names, seeds: seeds ?? AUDIT_SEEDS }),
        name: 'audit',
      },
    ],
  },
]
