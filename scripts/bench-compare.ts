/**
 * Interleaved in-process comparison of two source trees.
 *
 * Bundles each tree's batches (`createBatches` in `bench-workloads.ts`), then runs worker
 * processes that load both bundles and time one batch of each, alternating which
 * runs first, round after round. Each worker reports the median of per-round time ratios and a
 * bootstrap 90% interval. Every ratio is candidate time over baseline time: below 1 means the
 * candidate is faster. Workers alternate which bundle is imported first.
 *
 * Each process is a single JIT history: identical trees read 0.98 to 1.04 across processes, so
 * effects below about 3% are unresolved. It screens; confirm with `pnpm bench ab` to decide.
 *
 * Usage:
 *   pnpm bench compare --baseline <tree> [--candidate <tree>] [--scenario name]...
 *     [--processes 4] [--rounds 400] [--warmup 40]
 */

import { spawnSync } from 'node:child_process'
import { mkdtempSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import path from 'node:path'
import { parseArgs } from 'node:util'
import { type ScenarioName, selectScenarios } from './bench-workloads'
import { loadEsbuild } from './esbuild'

const ROOT = path.resolve(import.meta.dirname, '..')

/** Bundles one tree's batches; the batch definitions come from this checkout. */
function bundle(tree: string, outfile: string): void {
  loadEsbuild().buildSync({
    bundle: true,
    format: 'esm',
    logLevel: 'error',
    nodePaths: [path.join(ROOT, 'node_modules')],
    outfile,
    platform: 'node',
    stdin: {
      contents: `
import * as scenarios from ${JSON.stringify(path.join(tree, 'perf/scenarios.ts'))}
import * as api from ${JSON.stringify(path.join(tree, 'src/index.ts'))}
import { createBatches } from ${JSON.stringify(path.join(ROOT, 'scripts/bench-workloads.ts'))}
export const batches = createBatches(scenarios, api)
`,
      loader: 'ts',
      resolveDir: ROOT,
    },
    target: 'esnext',
  })
}

// Runs in a plain Node process: no loader, so both bundles see the same runtime.
const WORKER = `
const [candidatePath, baselinePath, scenario, roundsText, warmupText, order] = process.argv.slice(2)
const load = async (file) => (await import(file)).batches[scenario]()
let candidate, baseline
if (order === 'candidate-first') { candidate = await load(candidatePath); baseline = await load(baselinePath) }
else { baseline = await load(baselinePath); candidate = await load(candidatePath) }
const rounds = Number(roundsText), warmup = Number(warmupText)
for (let index = 0; index < warmup; index += 1) { candidate(); baseline() }
const ratios = []
for (let index = 0; index < rounds; index += 1) {
  let start, candidateTime, baselineTime
  if (index % 2 === 0) {
    start = performance.now(); candidate(); candidateTime = performance.now() - start
    start = performance.now(); baseline(); baselineTime = performance.now() - start
  } else {
    start = performance.now(); baseline(); baselineTime = performance.now() - start
    start = performance.now(); candidate(); candidateTime = performance.now() - start
  }
  ratios.push(candidateTime / baselineTime)
}
const median = (values) => {
  const sorted = [...values].sort((a, b) => a - b), middle = sorted.length >> 1
  return sorted.length % 2 === 1 ? sorted[middle] : (sorted[middle - 1] + sorted[middle]) / 2
}
let seed = 0x9e3779b9
const random = () => { seed ^= seed << 13; seed >>>= 0; seed ^= seed >>> 17; seed ^= seed << 5; seed >>>= 0; return seed / 4294967296 }
const resampled = []
// Percentile bootstrap with the same draws and indices as ab-time.py.
const draws = 2000
for (let draw = 0; draw < draws; draw += 1) resampled.push(median(Array.from(ratios, () => ratios[Math.floor(random() * ratios.length)])))
resampled.sort((a, b) => a - b)
console.log(JSON.stringify({ high: resampled[draws * 0.95 - 1], low: resampled[draws * 0.05], ratio: median(ratios) }))
`

// Builds and runs each selected batch of one bundle once, so a tree that lacks a scenario fails
// before any measurement.
const PREFLIGHT = `
const [file, ...names] = process.argv.slice(2)
const { batches } = await import(file)
for (const name of names) batches[name]()()
`

export interface CompareOptions {
  readonly baseline: string
  readonly candidate: string
  readonly processes: number
  readonly rounds: number
  readonly scenarios: readonly ScenarioName[]
  readonly warmup: number
}

function count(value: string, name: string, minimum: number): number {
  const result = Number(value)
  if (!Number.isSafeInteger(result) || result < minimum)
    throw new RangeError(`--${name} must be an integer >= ${minimum}`)
  return result
}

export function compareOptions(argv: string[]): CompareOptions {
  const { values } = parseArgs({
    args: argv,
    options: {
      baseline: { type: 'string' },
      candidate: { default: ROOT, type: 'string' },
      processes: { default: '4', type: 'string' },
      rounds: { default: '400', type: 'string' },
      scenario: { multiple: true, type: 'string' },
      warmup: { default: '40', type: 'string' },
    },
  })
  if (values.baseline === undefined) throw new Error('compare requires --baseline <source tree>')
  return {
    baseline: path.resolve(values.baseline),
    candidate: path.resolve(values.candidate),
    processes: count(values.processes, 'processes', 1),
    rounds: count(values.rounds, 'rounds', 1),
    scenarios: selectScenarios(values.scenario),
    warmup: count(values.warmup, 'warmup', 0),
  }
}

export interface Files {
  readonly baseline: string
  readonly candidate: string
  readonly preflight: string
  readonly worker: string
}

function node(arguments_: string[]): string {
  const result = spawnSync(process.execPath, arguments_, { encoding: 'utf8' })
  if (result.status !== 0) throw new Error(`${arguments_.join(' ')} failed:\n${result.stderr}`)
  return result.stdout
}

/** One worker process: the median ratio of `rounds` interleaved rounds and its 90% interval. */
export function measure(
  files: Files,
  scenario: string,
  options: Pick<CompareOptions, 'rounds' | 'warmup'>,
  order: 'baseline-first' | 'candidate-first',
): { high: number; low: number; ratio: number } {
  return JSON.parse(
    node([
      files.worker,
      files.candidate,
      files.baseline,
      scenario,
      String(options.rounds),
      String(options.warmup),
      order,
    ]),
  ) as { high: number; low: number; ratio: number }
}

/** Writes the worker scripts next to the bundles of a comparison. */
export function workerFiles(directory: string): Files {
  const files = {
    baseline: path.join(directory, 'baseline.mjs'),
    candidate: path.join(directory, 'candidate.mjs'),
    preflight: path.join(directory, 'preflight.mjs'),
    worker: path.join(directory, 'worker.mjs'),
  }
  writeFileSync(files.worker, WORKER)
  writeFileSync(files.preflight, PREFLIGHT)
  return files
}

function compare(argv: string[]): void {
  if (argv.includes('--help') || argv.includes('-h')) {
    console.log(
      'Usage: pnpm bench compare --baseline <tree> [--candidate <tree>] [--scenario name]...\n' +
        '  [--processes 4] [--rounds 400] [--warmup 40]',
    )
    return
  }
  const options = compareOptions(argv)
  const directory = mkdtempSync(path.join(tmpdir(), 'reconcile-bench-compare-'))
  try {
    const files = workerFiles(directory)
    bundle(options.candidate, files.candidate)
    bundle(options.baseline, files.baseline)
    for (const tree of [files.candidate, files.baseline])
      node([files.preflight, tree, ...options.scenarios])
    console.log('Ratios are candidate time / baseline time; below 1 means the candidate is faster.')
    console.log(
      `Each cell is one process: median of ${options.rounds} interleaved rounds [90% interval].`,
    )
    for (const scenario of options.scenarios) {
      const cells = Array.from({ length: options.processes }, (_, index) => {
        const { high, low, ratio } = measure(
          files,
          scenario,
          options,
          index % 2 === 0 ? 'candidate-first' : 'baseline-first',
        )
        return `${ratio.toFixed(3)} [${low.toFixed(3)}, ${high.toFixed(3)}]`
      })
      console.log(`${scenario.padEnd(24)} ${cells.join('  ')}`)
    }
  } finally {
    rmSync(directory, { force: true, recursive: true })
  }
}

if (process.argv[1] !== undefined && path.resolve(process.argv[1]) === import.meta.filename)
  compare(process.argv.slice(2))
