/**
 * Runtime profiling workflow.
 *
 * Bundles the profiling harness with esbuild, profiles one configured target,
 * prints the results to stdout, and preserves raw profiles, source maps,
 * configuration and a JSON summary for comparison or inspection.
 *
 * Usage:
 *   pnpm bench profile produce --batches 50 --out /tmp/profiles
 */

import assert from 'node:assert/strict'
import { createHash } from 'node:crypto'
import { execFileSync } from 'node:child_process'
import {
  existsSync,
  mkdirSync,
  mkdtempSync,
  readdirSync,
  readFileSync,
  writeFileSync,
} from 'node:fs'
import { SourceMap } from 'node:module'
import { tmpdir } from 'node:os'
import path from 'node:path'
import { parseArgs } from 'node:util'

import { instrumentCounts, counterSetup, counterReset, counterReport } from './profile-counts'
import { scenarioNames } from './bench-workloads'
import { loadEsbuild } from './esbuild'
import { diagnosticNames } from './profile-scenarios'
import { parseDeopts } from './profile-deopts'
import { parseCPUProfile, parseHeapProfile, type BundleMap } from './profile-frames'
import {
  generateReadingGuide,
  generateReport,
  rankRuntimeFrames,
  type ScenarioResult,
} from './profile-report'
import {
  comparisonMetrics,
  counterRecord,
  countsResult,
  readSampleMetrics,
  timeResult,
} from './profile-summary'
import { BATCH_SIZE } from '../perf/config'

interface ScenarioDefinition {
  name: string
}

interface TargetDefinition {
  name: string
}

type Mode = 'all' | 'counts' | 'cpu' | 'deopt' | 'heap' | 'time'
type PassMode = Exclude<Mode, 'all'>

interface WorkflowConfig {
  cpuProfIntervalUs: number
  diagnosticSize: number
  harnessSource: string
  heapProfIntervalBytes: number
  measurementBatchCount: number
  mode: Mode
  root: string
  scenarios: ScenarioDefinition[]
  target: TargetDefinition
  timeout: number
  traceBatchCountLimit: number
  warmupBatchCount: number
}

interface ScenarioArtifacts {
  cpuprofilePath: string
  heapprofilePath: string
  traceLogPath: string
}

interface ComparisonSample {
  directory: string
  label: 'baseline' | 'candidate'
  metrics: Record<string, number>
  round: number
}

type CounterSites = Record<string, Record<string, number>>

const ROOT = path.resolve(import.meta.dirname, '..')

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
    'pairs': { default: '5', type: 'string' },
    'size': { default: '256', type: 'string' },
    'timeout': { default: '120000', type: 'string' },
    'warmup': { default: '5', type: 'string' },
  },
})
const usage =
  'Usage: pnpm bench profile <scenario> [--mode time|counts|cpu|heap|deopt|all] [--batches N] [--warmup N] [--cpu-interval us] [--heap-interval bytes] [--timeout ms] [--out directory] [--candidate tree] [--baseline tree --pairs N] [--size N] [--bundle-only]\n' +
  '--baseline takes counts, cpu, heap or deopt; compare time with pnpm bench ab.'
if (values.help === true) {
  console.log(usage)
  console.log(
    `Scenarios: ${scenarioNames.join(', ')}\n` +
      'Diagnostic scenarios: ' +
      diagnosticNames.filter((name) => name.startsWith('diag-')).join(', '),
  )
  process.exit(0)
}
const targetArgument = positionals[0]
if (
  !['all', 'counts', 'cpu', 'deopt', 'heap', 'time'].includes(values.mode) ||
  (values.baseline !== undefined && values.mode === 'time') ||
  positionals.length !== 1 ||
  !([...scenarioNames, ...diagnosticNames] as readonly string[]).includes(targetArgument)
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
const target: TargetDefinition = { name: targetArgument }
const config: WorkflowConfig = {
  cpuProfIntervalUs: integer(values['cpu-interval'], 'cpu-interval'),
  diagnosticSize: integer(values.size, 'size'),
  harnessSource: path.join(path.resolve(values.candidate ?? ROOT), 'perf', 'profile-harness.ts'),
  heapProfIntervalBytes: integer(values['heap-interval'], 'heap-interval'),
  measurementBatchCount: integer(values.batches, 'batches'),
  mode: values.mode as Mode,
  root: path.resolve(values.candidate ?? ROOT),
  scenarios: [{ name: target.name }],
  target,
  timeout: integer(values.timeout, 'timeout'),
  traceBatchCountLimit: 200,
  warmupBatchCount: integer(values.warmup, 'warmup', 0),
}
const operations = config.measurementBatchCount * BATCH_SIZE

const outputParent = path.resolve(values.out ?? tmpdir())
mkdirSync(outputParent, { recursive: true })
const outputDirectory = mkdtempSync(path.join(outputParent, 'reconcile-profile-'))
const runId = path.basename(outputDirectory)
const startedAt = new Date().toISOString()
let complete = false

const digest = (content: string | Buffer): string =>
  createHash('sha256').update(content).digest('hex')

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
import { dateType } from ${JSON.stringify(path.join(config.root, 'src/types/date.ts'))}
import { arrayBufferType } from ${JSON.stringify(path.join(config.root, 'src/types/array-buffer.ts'))}
const copyOperations = { date: dateType.policy.immutable.operations, buffer: arrayBufferType.policy.immutable.operations }
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
  snapshot: api.snapshot, ...serialization,
  copyDate: copyOperations.date.copy, sameBuffer: copyOperations.buffer.equivalent }, ${config.diagnosticSize})
console.log('RECONCILE_DIAGNOSTIC ' + JSON.stringify(diagnostic.metadata))
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
  const harness = (diagnosticNames as readonly string[]).includes(target.name)
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

/** The nearest package.json at or above the directory of `file`. */
function packageManifest(file: string): string | undefined {
  let directory = path.dirname(file)
  while (directory !== path.dirname(directory)) {
    const manifest = path.join(directory, 'package.json')
    if (existsSync(manifest)) return manifest
    directory = path.dirname(directory)
  }
  return undefined
}

function packageRecord(manifest: string) {
  const parsed = JSON.parse(readFileSync(manifest, 'utf8')) as {
    name?: string
    version?: string
  }
  return {
    name: parsed.name,
    sha256: digest(readFileSync(manifest)),
    version: parsed.version,
  }
}

/** Digests every bundled input and records the package that owns it. */
function bundleInputs(metafileInputs: Record<string, unknown>, original: string) {
  const inputs: Record<string, string> = { [config.harnessSource]: digest(original) }
  const packages: Record<string, unknown> = {}
  for (const input of Object.keys(metafileInputs)) {
    const file = path.resolve(input)
    if (!existsSync(file)) continue
    inputs[file] = digest(readFileSync(file))
    const manifest = packageManifest(file)
    if (manifest !== undefined) packages[manifest] = packageRecord(manifest)
  }
  return { inputs, packages }
}

const isProfileTool = (name: string): boolean =>
  (name.startsWith('profile') && /\.(?:py|ts)$/.test(name)) || name === 'bounded-check.py'

function toolSources() {
  return Object.fromEntries(
    readdirSync(import.meta.dirname)
      .filter(isProfileTool)
      .map((name) => [name, digest(readFileSync(path.join(import.meta.dirname, name)))]),
  )
}

async function bundleHarness(): Promise<{ bundlePath: string; sourceMap: SourceMap }> {
  const bundlePath = path.join(outputDirectory, 'harness.mjs')
  const original = readFileSync(config.harnessSource, 'utf8')
  assert.equal(original.split(MEASUREMENT).length, 2, 'Frozen harness measurement marker changed')
  // Tool-only overlay: the frozen workload and its warmup/measurement loops stay intact.
  // Phase markers and timer reads run outside the measured loop. No inspector in time mode.
  const contents = harnessOverlay(original)
  const counterSites: CounterSites = {}
  writeFileSync(path.join(outputDirectory, 'harness-source.ts'), contents)
  const esbuild = loadEsbuild()
  const options = {
    bundle: true,
    format: 'esm',
    metafile: true,
    nodePaths: [path.join(ROOT, 'node_modules')],
    outfile: bundlePath,
    platform: 'node',
    sourcemap: true,
    target: 'esnext',
  }
  const { metafile } = await esbuild.build({
    plugins: counterPlugins(counterSites),
    ...options,
    stdin: {
      contents,
      loader: 'ts',
      resolveDir: path.dirname(config.harnessSource),
      sourcefile: config.harnessSource,
    },
  })
  const { inputs, packages } = bundleInputs(metafile.inputs, original)
  writeFileSync(
    path.join(outputDirectory, 'build.json'),
    JSON.stringify(
      {
        bundleSha256: digest(readFileSync(bundlePath)),
        counterSites,
        esbuild: esbuild.version,
        inputs,
        options,
        overlaySha256: digest(contents),
        packages,
        sourceMapSha256: digest(readFileSync(`${bundlePath}.map`)),
        toolSha256: digest(readFileSync(import.meta.filename)),
        toolSources: toolSources(),
        versions: process.versions,
      },
      null,
      2,
    ) + '\n',
  )
  const rawMap = JSON.parse(
    readFileSync(`${bundlePath}.map`, 'utf8'),
  ) as import('node:module').SourceMapPayload
  return { bundlePath, sourceMap: new SourceMap(rawMap) }
}

const isSampled = (mode: PassMode): boolean => mode === 'cpu' || mode === 'heap'

/** The trace pass runs at most `traceBatchCountLimit` measurement batches. */
const passBatchCount = (mode: PassMode): number =>
  mode === 'deopt'
    ? Math.min(config.measurementBatchCount, config.traceBatchCountLimit)
    : config.measurementBatchCount

function samplerArguments(mode: PassMode, profile: string): string[] {
  if (!isSampled(mode)) return []
  return [
    mode,
    profile,
    String(mode === 'cpu' ? config.cpuProfIntervalUs : config.heapProfIntervalBytes),
  ]
}

function passArguments(
  scenario: string,
  bundlePath: string,
  mode: PassMode,
  profile: string,
): string[] {
  return [
    ...(mode === 'deopt' ? ['--trace-opt', '--trace-deopt'] : []),
    bundlePath,
    scenario,
    String(passBatchCount(mode)),
    String(config.warmupBatchCount),
    ...samplerArguments(mode, profile),
  ]
}

/** A captured child-process stream from a failed `execFileSync`, or empty when absent. */
const processStream = (error: unknown, stream: 'stderr' | 'stdout'): string =>
  error !== null && typeof error === 'object' && stream in error
    ? String(Reflect.get(error, stream))
    : ''

function recordScenarioMetadata(stdout: string): void {
  const scenario = stdout.split('\n').find((line) => line.startsWith('RECONCILE_DIAGNOSTIC '))
  if (scenario !== undefined)
    writeFileSync(
      path.join(outputDirectory, 'scenario.json'),
      JSON.stringify(JSON.parse(scenario.slice('RECONCILE_DIAGNOSTIC '.length)), null, 2) + '\n',
    )
}

function runPass(scenario: string, bundlePath: string, mode: PassMode): string {
  const rawDirectory = path.join(outputDirectory, 'raw')
  mkdirSync(rawDirectory, { recursive: true })
  const profile = path.join(
    rawDirectory,
    `${scenario}.${mode === 'cpu' ? 'cpuprofile' : 'heapprofile'}`,
  )
  const output = path.join(rawDirectory, `${scenario}.${mode}.log`)
  const arguments_ = passArguments(scenario, bundlePath, mode, profile)
  try {
    const stdout = execFileSync(process.execPath, arguments_, {
      cwd: config.root,
      encoding: 'utf8',
      env: { ...process.env, NODE_NO_WARNINGS: '1' },
      maxBuffer: 50 * 1024 * 1024,
      timeout: config.timeout,
    })
    writeFileSync(output, stdout)
    recordScenarioMetadata(stdout)
  } catch (error: unknown) {
    const stderr = processStream(error, 'stderr')
    const stdout = processStream(error, 'stdout')
    writeFileSync(output, stdout + '\n' + stderr)
    throw error
  }
  return isSampled(mode) ? profile : output
}

function runScenario(scenario: string, bundlePath: string): ScenarioArtifacts {
  return {
    cpuprofilePath: runPass(scenario, bundlePath, 'cpu'),
    heapprofilePath: runPass(scenario, bundlePath, 'heap'),
    traceLogPath: runPass(scenario, bundlePath, 'deopt'),
  }
}

/** Child-process arguments that profile one comparison sample of `source`. */
function sampleArguments(source: string, destination: string): string[] {
  return [
    ...process.execArgv,
    import.meta.filename,
    target.name,
    '--candidate',
    source,
    '--size',
    String(config.diagnosticSize),
    '--mode',
    config.mode,
    '--batches',
    String(config.measurementBatchCount),
    '--warmup',
    String(config.warmupBatchCount),
    '--cpu-interval',
    String(config.cpuProfIntervalUs),
    '--heap-interval',
    String(config.heapProfIntervalBytes),
    '--timeout',
    String(config.timeout),
    '--out',
    destination,
  ]
}

function runSampleProcess(arguments_: string[], destination: string): void {
  try {
    const output = execFileSync(process.execPath, arguments_, {
      cwd: ROOT,
      encoding: 'utf8',
      maxBuffer: 50 * 1024 * 1024,
      timeout: config.timeout * 4,
    })
    writeFileSync(path.join(destination, 'process.log'), output)
  } catch (error: unknown) {
    writeFileSync(path.join(destination, 'process.log'), String(error))
    throw error
  }
}

function collectSample(
  round: number,
  label: 'baseline' | 'candidate',
  source: string,
): ComparisonSample {
  const destination = path.join(outputDirectory, `${round}-${label}`)
  mkdirSync(destination)
  runSampleProcess(sampleArguments(source, destination), destination)
  const children = readdirSync(destination).filter((name) => name.startsWith('reconcile-profile-'))
  assert.equal(children.length, 1)
  const directory = path.join(destination, children[0])
  return { directory, label, metrics: readSampleMetrics(directory, operations), round }
}

/** Alternates which source runs first in each round. */
const roundOrder = (round: number) =>
  round % 2 === 0 ? (['candidate', 'baseline'] as const) : (['baseline', 'candidate'] as const)

function compareSources(): void {
  const pairs = integer(values.pairs, 'pairs', 2)
  const samples: ComparisonSample[] = []
  const roots = { baseline: path.resolve(values.baseline!), candidate: config.root }
  // Persist each completed sample: a failed later subprocess cannot erase earlier evidence.
  for (let round = 0; round < pairs; round += 1) {
    for (const label of roundOrder(round)) {
      samples.push(collectSample(round, label, roots[label]))
      writeFileSync(
        path.join(outputDirectory, 'samples.json'),
        JSON.stringify(samples, null, 2) + '\n',
      )
    }
  }
  const metrics = comparisonMetrics(samples)
  const comparison = { metrics, mode: config.mode, pairs, roots, samples }
  writeFileSync(
    path.join(outputDirectory, 'comparison.json'),
    JSON.stringify(comparison, null, 2) + '\n',
  )
  writeFileSync(
    path.join(outputDirectory, 'report.md'),
    `# Alternating process comparison\n\nRaw observations and median/min/max: [comparison.json](comparison.json).\n\nEach sample uses a separate warmed process. Profiled time and sampled allocation are diagnostics; time mode measures loop latency without an active profiler. No significance or speedup claim is inferred automatically.\n`,
  )
  console.log(JSON.stringify({ metrics, mode: config.mode, pairs, roots }, null, 2))
}

function readCounterSites(): CounterSites {
  const build = JSON.parse(readFileSync(path.join(outputDirectory, 'build.json'), 'utf8')) as {
    counterSites: CounterSites
  }
  return build.counterSites
}

/** Builds the summary result of one selected pass from its raw artifact. */
const passResults: Record<PassMode, (artifact: string, bundle: BundleMap) => unknown> = {
  counts: (artifact) =>
    countsResult(counterRecord(readFileSync(artifact, 'utf8')), readCounterSites(), operations),
  cpu: (artifact, bundle) => {
    const cpu = parseCPUProfile(artifact, bundle)
    return { ...cpu, frames: [...cpu.frames.values()] }
  },
  deopt: (artifact) => ({
    ...parseDeopts(readFileSync(artifact, 'utf8')),
    scope: 'Setup, warmup, measurement and completion; see phase markers in raw log.',
  }),
  heap: (artifact, bundle) => {
    const heap = parseHeapProfile(artifact, bundle)
    return { allocations: [...heap.frames.values()], attribution: heap.attribution }
  },
  time: (artifact) => timeResult(readFileSync(artifact, 'utf8'), operations),
}

function runSelectedPass(mode: PassMode, bundle: BundleMap): void {
  const artifact = runPass(config.target.name, bundle.bundlePath, mode)
  const result = passResults[mode](artifact, bundle)
  const summary = { artifact, mode: config.mode, result }
  writeFileSync(path.join(outputDirectory, 'summary.json'), JSON.stringify(summary, null, 2) + '\n')
  writeFileSync(
    path.join(outputDirectory, 'report.md'),
    `# ${config.target.name}: ${config.mode}\n\nOnly the selected pass was measured. Raw artifact: ${artifact}\n\n\`\`\`json\n${JSON.stringify(result, null, 2)}\n\`\`\`\n`,
  )
  console.log(JSON.stringify(summary, null, 2))
}

function profileScenario(name: string, bundle: BundleMap): ScenarioResult {
  const artifacts = runScenario(name, bundle.bundlePath)
  const cpuResult = parseCPUProfile(artifacts.cpuprofilePath, bundle)

  const heapResult = parseHeapProfile(artifacts.heapprofilePath, bundle)
  const deoptResult = parseDeopts(readFileSync(artifacts.traceLogPath, 'utf8'))
  return {
    allocFrames: heapResult.frames,
    cpuAttribution: cpuResult.attribution,
    cpuprofilePath: artifacts.cpuprofilePath,
    deoptCoverage: deoptResult.coverage,
    deopts: deoptResult.entries,
    frames: cpuResult.frames,
    gcTimeUs: cpuResult.gcTimeUs,
    heapAttribution: heapResult.attribution,
    heapprofilePath: artifacts.heapprofilePath,
    scenario: name,
    totalTime: cpuResult.totalTime,
    traceLogPath: artifacts.traceLogPath,
  }
}

function runAllPasses(bundle: BundleMap): void {
  const results = new Map<string, ScenarioResult>()

  console.log(
    `  [run]  ${config.measurementBatchCount.toLocaleString()} measurement batches, ${config.warmupBatchCount.toLocaleString()} warmup batches, ${BATCH_SIZE} ops/batch`,
  )

  for (const { name } of config.scenarios) results.set(name, profileScenario(name, bundle))

  console.log('')

  const runtime = results.get(config.target.name)

  assert(runtime !== undefined, `scenario "${config.target.name}" not found in results`)

  const ranked = rankRuntimeFrames(runtime, operations)

  console.log(`===== ${config.target.name.toUpperCase()} =====`)
  console.log('')
  console.log(generateReadingGuide(config.target.name))
  console.log('')
  const report = generateReport(config.target.name, runtime, ranked, config.measurementBatchCount)
  writeFileSync(path.join(outputDirectory, 'report.md'), report + '\n')
  writeFileSync(
    path.join(outputDirectory, 'summary.json'),
    JSON.stringify(
      {
        allocations: [...runtime.allocFrames.values()],
        cpuAttribution: runtime.cpuAttribution,
        deoptCoverage: runtime.deoptCoverage,
        deopts: runtime.deopts,
        gcTimeUs: runtime.gcTimeUs,
        heapAttribution: runtime.heapAttribution,
        operations,
        profiledTimeUs: runtime.totalTime,
        ranked,
      },
      null,
      2,
    ) + '\n',
  )
  console.log(report)
  console.log('')
}

async function runWorkflow(): Promise<void> {
  console.log('Context-runtime profiling workflow')
  console.log(`Run ID:  ${runId}`)
  console.log(`Artifacts: ${outputDirectory}`)
  console.log('')
  if (values.baseline !== undefined) {
    compareSources()
    return
  }
  console.log('  [build] bundling harness with esbuild')

  const { bundlePath, sourceMap } = await bundleHarness()
  if (values['bundle-only'] === true) {
    // Alternating rounds reuse one frozen bundle per source tree instead of rebundling per sample.
    console.log(`RECONCILE_BUNDLE ${bundlePath}`)
    return
  }
  const bundle: BundleMap = { bundlePath, root: config.root, sourceMap }
  if (config.mode === 'all') runAllPasses(bundle)
  else runSelectedPass(config.mode, bundle)
}

try {
  await runWorkflow()
  complete = true
  console.log('Done.')
} finally {
  writeFileSync(
    path.join(outputDirectory, 'run.json'),
    JSON.stringify(
      {
        comparison:
          values.baseline === undefined
            ? undefined
            : {
                baseline: path.resolve(values.baseline),
                pairs: integer(values.pairs, 'pairs', 2),
              },
        config,
        finishedAt: new Date().toISOString(),
        node: process.version,
        startedAt,
        status: complete ? 'complete' : 'failed',
        v8: process.versions.v8,
      },
      null,
      2,
    ) + '\n',
  )
}
