/**
 * Runtime profiling workflow.
 *
 * Bundles the profiling harness with esbuild, runs one pass of one scenario, prints its summary
 * and keeps the summary, the raw artifact and the bundle with its source map. With `--baseline`,
 * counts mode runs each tree once and reports the counters that differ.
 *
 * Usage:
 *   pnpm bench profile produce --batches 50 --out /tmp/profiles
 */

import assert from 'node:assert/strict'
import { execFileSync } from 'node:child_process'
import { mkdirSync, mkdtempSync, readdirSync, readFileSync, writeFileSync } from 'node:fs'
import { SourceMap } from 'node:module'
import { tmpdir } from 'node:os'
import path from 'node:path'
import { parseArgs } from 'node:util'

import type { WeightedFrame } from './profile-attribution'
import { counterReport, counterReset, counterSetup, instrumentCounts } from './profile-counts'
import { scenarioNames } from './bench-workloads'
import { loadEsbuild } from './esbuild'
import { diagnosticNames } from './profile-scenarios'
import { parseDeopts } from './profile-deopts'
import { parseCPUProfile, parseHeapProfile, type BundleMap } from './profile-frames'
import { counterRecord, countChanges, countsResult } from './profile-summary'
import { BATCH_SIZE } from '../perf/config'

const modes = ['counts', 'cpu', 'deopt', 'heap'] as const
type Mode = (typeof modes)[number]

type CounterSites = Record<string, Record<string, number>>

/** The bundled harness and, in counts mode, the counter sites of each instrumented source. */
interface HarnessBundle extends BundleMap {
  readonly counterSites: CounterSites
}

const ROOT = path.resolve(import.meta.dirname, '..')

/** The trace pass runs at most this many measurement batches. */
const TRACE_BATCH_LIMIT = 200

const { positionals, values } = parseArgs({
  allowPositionals: true,
  options: {
    'baseline': { type: 'string' },
    'batches': { default: '200', type: 'string' },
    'bundle-only': { type: 'boolean' },
    'candidate': { type: 'string' },
    'cpu-interval': { default: '1000', type: 'string' },
    'heap-interval': { default: '32768', type: 'string' },
    'help': { short: 'h', type: 'boolean' },
    'mode': { default: 'cpu', type: 'string' },
    'out': { type: 'string' },
    'size': { default: '256', type: 'string' },
    'warmup': { default: '5', type: 'string' },
  },
})
const usage =
  'Usage: pnpm bench profile <scenario> [--mode cpu|counts|heap|deopt] [--batches N] [--warmup N] [--cpu-interval us] [--heap-interval bytes] [--out directory] [--candidate tree] [--baseline tree] [--size N] [--bundle-only]\n' +
  '--baseline takes counts mode only and reports the counters that differ; compare time with pnpm bench ab.'
if (values.help === true) {
  console.log(usage)
  console.log(
    `Scenarios: ${scenarioNames.join(', ')}\n` +
      'Diagnostic scenarios: ' +
      diagnosticNames.filter((name) => name.startsWith('diag-')).join(', '),
  )
  process.exit(0)
}
const scenario = positionals[0]
if (
  !(modes as readonly string[]).includes(values.mode) ||
  (values.baseline !== undefined && values.mode !== 'counts') ||
  positionals.length !== 1 ||
  !([...scenarioNames, ...diagnosticNames] as readonly string[]).includes(scenario)
) {
  console.error(usage)
  process.exit(1)
}
function integer(value: string, name: string, minimum = 1): number {
  const result = Number(value)
  if (!Number.isSafeInteger(result) || result < minimum)
    throw new RangeError(`${name} must be an integer >= ${minimum}`)
  return result
}
const root = path.resolve(values.candidate ?? ROOT)
const config = {
  cpuProfIntervalUs: integer(values['cpu-interval'], 'cpu-interval'),
  diagnosticSize: integer(values.size, 'size'),
  harnessSource: path.join(root, 'perf', 'profile-harness.ts'),
  heapProfIntervalBytes: integer(values['heap-interval'], 'heap-interval'),
  measurementBatchCount: integer(values.batches, 'batches'),
  mode: values.mode as Mode,
  root,
  warmupBatchCount: integer(values.warmup, 'warmup', 0),
}
const operations = config.measurementBatchCount * BATCH_SIZE

const outputParent = path.resolve(values.out ?? tmpdir())
mkdirSync(outputParent, { recursive: true })
const outputDirectory = mkdtempSync(path.join(outputParent, 'reconcile-profile-'))

const MEASUREMENT = 'for (let index = 0; index < batchCount; index += 1) run()'

/** Replaces the frozen scenario imports and registry with the selected diagnostic scenario. */
function diagnosticOverlay(original: string): string {
  const importsStart = original.indexOf('import {\n  createContextRuntime')
  const importsEnd =
    original.indexOf("} from './scenarios'", importsStart) + "} from './scenarios'".length
  assert(importsStart >= 0 && importsEnd > importsStart, 'Frozen scenario imports changed')
  const harness =
    original.slice(0, importsStart) +
    `
import { createDiagnostic } from ${JSON.stringify(path.join(ROOT, 'scripts/profile-scenarios.ts'))}
import * as api from ${JSON.stringify(path.join(config.root, 'src/index.ts'))}
` +
    original.slice(importsEnd)
  const registryStart = harness.indexOf('const profileScenarios:')
  const registryEnd = harness.indexOf('const run = profileScenarios', registryStart)
  assert(registryStart >= 0 && registryEnd > registryStart, 'Frozen scenario registry changed')
  return (
    harness.slice(0, registryStart) +
    `
// Trees from before serialization lack these exports and reject the serialization scenarios.
const serialization = { deserialize: Reflect.get(api, 'deserialize'),
  requiredMaxBytes: Reflect.get(api, 'requiredMaxBytes'), serialize: Reflect.get(api, 'serialize') }
const diagnostic = createDiagnostic(scenario, { produce: api.produce, reconcile: api.reconcile,
  snapshot: api.snapshot, ...serialization }, ${config.diagnosticSize})
const profileScenarios = { [scenario]: () => () => {
  for (let operation = 0; operation < BATCH_SIZE; operation += 1) diagnostic.run()
} }
` +
    harness.slice(registryEnd) +
    '\ndiagnostic.validate()\n'
  )
}

/** Phase markers and timer reads, all outside the measured loop. */
function phaseOverlay(harness: string): string {
  return harness
    .replace(
      MEASUREMENT,
      `
if (mode === undefined) console.log('RECONCILE_PHASE measurement')
const measurementStart = mode === undefined ? performance.now() : 0
${MEASUREMENT}
const elapsedMs = mode === undefined ? performance.now() - measurementStart : 0
`,
    )
    .replace(
      'const run = profileScenarios',
      "console.log('RECONCILE_PHASE setup')\nconst run = profileScenarios",
    )
    .replace(
      'for (let index = 0; index < warmupCount;',
      "console.log('RECONCILE_PHASE warmup')\nfor (let index = 0; index < warmupCount;",
    )
    .replace(
      'const session = new Session()',
      "if (mode !== undefined) console.log('RECONCILE_PHASE measurement')\nconst session = new Session()",
    )
    .replace(
      'console.log(\n  `Profiled',
      "if (mode === undefined) console.log('RECONCILE_TIME ' + JSON.stringify({ elapsedMs, operations: batchCount * BATCH_SIZE }))\nconsole.log('RECONCILE_PHASE complete')\nconsole.log(\n  `Profiled",
    )
}

/** Counter setup before the scenario, a reset before measurement and a report after it. */
function counterOverlay(contents: string): string {
  return contents
    .replace('const run = profileScenarios', counterSetup + 'const run = profileScenarios')
    .replace('const measurementStart =', counterReset + 'const measurementStart =')
    .replace(
      "console.log('RECONCILE_PHASE complete')",
      counterReport + "console.log('RECONCILE_PHASE complete')",
    )
}

function harnessOverlay(original: string): string {
  const harness = (diagnosticNames as readonly string[]).includes(scenario)
    ? diagnosticOverlay(original)
    : original
  const contents = phaseOverlay(harness)
  return config.mode === 'counts' ? counterOverlay(contents) : contents
}

/** Instruments one library source for the counts bundle and keeps the overlay for inspection. */
function instrumentSource(file: string, counterSites: CounterSites) {
  const relative = path.relative(config.root, file)
  if (!relative.startsWith('src/') || relative.startsWith('src/__tests__/')) return undefined
  const transformed = instrumentCounts(readFileSync(file, 'utf8'), relative)
  counterSites[relative] = transformed.sites
  const destination = path.join(outputDirectory, 'instrumented', relative)
  mkdirSync(path.dirname(destination), { recursive: true })
  writeFileSync(destination, transformed.contents)
  return {
    contents: transformed.contents,
    loader: 'ts',
    resolveDir: path.dirname(file),
  }
}

function counterPlugins(counterSites: CounterSites) {
  return config.mode !== 'counts'
    ? []
    : [
        {
          name: 'diagnostic-counters',
          setup(build: {
            onLoad: (
              options: { filter: RegExp },
              callback: (arguments_: { path: string }) => unknown,
            ) => void
          }) {
            build.onLoad({ filter: /\.ts$/ }, ({ path: file }) =>
              instrumentSource(file, counterSites),
            )
          },
        },
      ]
}

async function bundleHarness(): Promise<HarnessBundle> {
  const bundlePath = path.join(outputDirectory, 'harness.mjs')
  const original = readFileSync(config.harnessSource, 'utf8')
  assert.equal(original.split(MEASUREMENT).length, 2, 'Frozen harness measurement marker changed')
  // Tool-only overlay: the frozen workload and its warmup/measurement loops stay intact.
  // Phase markers and timer reads run outside the measured loop.
  const contents = harnessOverlay(original)
  const counterSites: CounterSites = {}
  writeFileSync(path.join(outputDirectory, 'harness-source.ts'), contents)
  await loadEsbuild().build({
    bundle: true,
    format: 'esm',
    nodePaths: [path.join(ROOT, 'node_modules')],
    outfile: bundlePath,
    platform: 'node',
    plugins: counterPlugins(counterSites),
    sourcemap: true,
    stdin: {
      contents,
      loader: 'ts',
      resolveDir: path.dirname(config.harnessSource),
      sourcefile: config.harnessSource,
    },
    target: 'esnext',
  })
  const rawMap = JSON.parse(
    readFileSync(`${bundlePath}.map`, 'utf8'),
  ) as import('node:module').SourceMapPayload
  return { bundlePath, counterSites, root: config.root, sourceMap: new SourceMap(rawMap) }
}

const isSampled = (mode: Mode): boolean => mode === 'cpu' || mode === 'heap'

/** The sampler's mode, profile path and interval, for cpu and heap only. */
function samplerArguments(profile: string): string[] {
  const { mode } = config
  if (!isSampled(mode)) return []
  return [
    mode,
    profile,
    String(mode === 'cpu' ? config.cpuProfIntervalUs : config.heapProfIntervalBytes),
  ]
}

function passArguments(bundlePath: string, profile: string): string[] {
  const trace = config.mode === 'deopt'
  return [
    ...(trace ? ['--trace-opt', '--trace-deopt'] : []),
    bundlePath,
    scenario,
    String(Math.min(config.measurementBatchCount, trace ? TRACE_BATCH_LIMIT : Infinity)),
    String(config.warmupBatchCount),
    ...samplerArguments(profile),
  ]
}

/** A captured child-process stream from a failed `execFileSync`, or empty when absent. */
const processStream = (error: unknown, stream: 'stderr' | 'stdout'): string =>
  error !== null && typeof error === 'object' && stream in error
    ? String(Reflect.get(error, stream))
    : ''

/** Runs the selected pass; its sampled profile, or its log for counts and deopt. */
function runPass(bundlePath: string): string {
  const rawDirectory = path.join(outputDirectory, 'raw')
  mkdirSync(rawDirectory, { recursive: true })
  const { mode } = config
  const profile = path.join(
    rawDirectory,
    `${scenario}.${mode === 'cpu' ? 'cpuprofile' : 'heapprofile'}`,
  )
  const output = path.join(rawDirectory, `${scenario}.${mode}.log`)
  try {
    const stdout = execFileSync(process.execPath, passArguments(bundlePath, profile), {
      cwd: config.root,
      encoding: 'utf8',
      env: { ...process.env, NODE_NO_WARNINGS: '1' },
      maxBuffer: 50 * 1024 * 1024,
    })
    writeFileSync(output, stdout)
  } catch (error: unknown) {
    const stderr = processStream(error, 'stderr')
    const stdout = processStream(error, 'stdout')
    writeFileSync(output, stdout + '\n' + stderr)
    throw error
  }
  return isSampled(mode) ? profile : output
}

/** Frames by self weight, heaviest first. */
const bySelf = <T extends { frames: WeightedFrame[] }>(attribution: T): T => ({
  ...attribution,
  frames: attribution.frames.toSorted((left, right) => right.self - left.self),
})

/** Builds the summary result of the selected pass from its raw artifact. */
const passResults: Record<Mode, (artifact: string, bundle: HarnessBundle) => unknown> = {
  counts: (artifact, bundle) =>
    countsResult(counterRecord(readFileSync(artifact, 'utf8')), bundle.counterSites, operations),
  cpu: (artifact, bundle) => {
    const cpu = parseCPUProfile(artifact, bundle)
    return { ...cpu, attribution: bySelf(cpu.attribution) }
  },
  deopt: (artifact) => ({
    ...parseDeopts(readFileSync(artifact, 'utf8')),
    scope: 'Setup, warmup, measurement and completion; see phase markers in raw log.',
  }),
  heap: (artifact, bundle) => bySelf(parseHeapProfile(artifact, bundle)),
}

/** Counts each tree once in a child process of this script and reports the counters that differ;
 * counts are exact, so one run per tree decides. */
function compareCounts(): void {
  const roots = { baseline: path.resolve(values.baseline!), candidate: config.root }
  const counts = Object.fromEntries(
    Object.entries(roots).map(([label, source]) => {
      const destination = path.join(outputDirectory, label)
      mkdirSync(destination)
      execFileSync(
        process.execPath,
        [
          ...process.execArgv,
          import.meta.filename,
          scenario,
          ...['--candidate', source, '--mode', 'counts', '--size', String(config.diagnosticSize)],
          ...['--batches', String(config.measurementBatchCount)],
          ...['--warmup', String(config.warmupBatchCount), '--out', destination],
        ],
        { cwd: ROOT, encoding: 'utf8', maxBuffer: 50 * 1024 * 1024 },
      )
      const [run] = readdirSync(destination)
      const summary = JSON.parse(
        readFileSync(path.join(destination, run, 'summary.json'), 'utf8'),
      ) as { result: { counts: Record<string, number> } }
      return [label, summary.result.counts]
    }),
  )
  const comparison = { changed: countChanges(counts.baseline, counts.candidate), operations, roots }
  writeFileSync(
    path.join(outputDirectory, 'comparison.json'),
    JSON.stringify(comparison, null, 2) + '\n',
  )
  console.log(JSON.stringify(comparison, null, 2))
}

async function runWorkflow(): Promise<void> {
  console.log(`Artifacts: ${outputDirectory}`)
  if (values.baseline !== undefined) {
    compareCounts()
    return
  }
  const bundle = await bundleHarness()
  if (values['bundle-only'] === true) {
    // Alternating rounds reuse one frozen bundle per source tree instead of rebundling per sample.
    console.log(`RECONCILE_BUNDLE ${bundle.bundlePath}`)
    return
  }
  const artifact = runPass(bundle.bundlePath)
  const summary = {
    artifact,
    mode: config.mode,
    result: passResults[config.mode](artifact, bundle),
  }
  writeFileSync(path.join(outputDirectory, 'summary.json'), JSON.stringify(summary, null, 2) + '\n')
  console.log(JSON.stringify(summary, null, 2))
}

await runWorkflow()
