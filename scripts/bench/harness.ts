import assert from 'node:assert/strict'
import { spawnSync } from 'node:child_process'
import { mkdirSync, readFileSync, realpathSync, writeFileSync } from 'node:fs'
import { SourceMap, type SourceMapPayload } from 'node:module'
import path from 'node:path'
import { build, type Plugin } from 'rolldown'
import { packageEntry } from '../bundles'
import { ROOT } from '../framework/paths'
import { virtualModule } from '../rolldown'
import type { BundleMap } from './frames'

/** The counter sites of each instrumented source file, by counter. */
export type CounterSites = Record<string, Record<string, number>>

/** A bundled harness and, when it counts, the counter sites of each instrumented source. */
export interface Harness extends BundleMap {
  readonly counterSites: CounterSites
}

/** What makes a harness count: the instrumentation of each source of the tree, and the harness
 * statements that set the counters up, reset them before measurement and report them after it. */
export interface Counting {
  readonly report: string
  readonly reset: string
  readonly setup: string
  readonly instrument: (
    source: string,
    file: string,
  ) => { readonly contents: string; readonly sites: Record<string, number> }
}

export interface HarnessOptions {
  /** Counts with this instrumentation; without it the harness only times. */
  readonly counting: Counting | undefined
  /** Where the bundle, its map and the overlaid harness source are written. */
  readonly directory: string
  /** Runs the scenario through the diagnostic overlay instead of the frozen harness. */
  readonly overlay: boolean
  /** Measures the tree's built package, which must be built, instead of its sources. */
  readonly package: boolean
  /** The diagnostics' size. */
  readonly size: number
  /** The source tree measured: its frozen harness and its `src/`. */
  readonly tree: string
}

const MEASUREMENT = 'for (let index = 0; index < batchCount; index += 1) run()'

/** Replaces the frozen scenario imports and registry with the diagnostic that the harness's
 * first argument names, built from this checkout's diagnostics and the tree's API. */
function diagnosticOverlay(original: string, { size, tree }: HarnessOptions): string {
  const importsStart = original.indexOf('import {\n  createContextRuntime')
  const importsEnd =
    original.indexOf("} from './scenarios'", importsStart) + "} from './scenarios'".length
  assert(importsStart >= 0 && importsEnd > importsStart, 'Frozen scenario imports changed')
  const harness =
    original.slice(0, importsStart) +
    `
import { createDiagnostic } from ${JSON.stringify(path.join(ROOT, 'scripts/bench/diagnostics.ts'))}
import * as api from ${JSON.stringify(path.join(tree, 'src/index.ts'))}
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
  snapshot: api.snapshot, ...serialization }, ${size})
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
function counterOverlay(contents: string, { report, reset, setup }: Counting): string {
  return contents
    .replace('const run = profileScenarios', setup + 'const run = profileScenarios')
    .replace('const measurementStart =', reset + 'const measurementStart =')
    .replace(
      "console.log('RECONCILE_PHASE complete')",
      report + "console.log('RECONCILE_PHASE complete')",
    )
}

/** Instruments one library source for the counts bundle and keeps the result for inspection. */
function instrumentSource(
  file: string,
  counting: Counting,
  options: HarnessOptions,
  counterSites: CounterSites,
) {
  const relative = path.relative(options.tree, file)
  if (!relative.startsWith('src/') || relative.startsWith('src/__tests__/')) return undefined
  const transformed = counting.instrument(readFileSync(file, 'utf8'), relative)
  counterSites[relative] = transformed.sites
  const destination = path.join(options.directory, 'instrumented', relative)
  mkdirSync(path.dirname(destination), { recursive: true })
  writeFileSync(destination, transformed.contents)
  return { code: transformed.contents, moduleType: 'ts' as const }
}

/** The plugin that instruments the tree's sources when the harness counts. */
function counterPlugins(options: HarnessOptions, counterSites: CounterSites): Plugin[] {
  const { counting } = options
  if (counting === undefined) return []
  return [
    {
      load: {
        filter: { id: /\.ts$/ },
        handler: (file) => instrumentSource(file, counting, options, counterSites),
      },
      name: 'diagnostic-counters',
    },
  ]
}

/** The library entry modules that the workloads and the diagnostic overlay import. */
const ENTRIES = ['index.ts', 'reconcile.ts', 'snapshot.ts']

/** The plugin that serves the tree's built package for the library's entry modules, so that a
 * round measures what the package ships. */
function packagePlugin(tree: string): Plugin {
  const entries = new Set(ENTRIES.map((file) => path.join(tree, 'src', file)))
  const built = packageEntry(tree)
  return {
    name: 'built-package',
    resolveId: {
      filter: { id: /[/\\]src[/\\](?:index|reconcile|snapshot)(?:\.ts)?$/ },
      async handler(source, importer, options) {
        const resolved = await this.resolve(source, importer, { ...options, skipSelf: true })
        return resolved !== null && entries.has(resolved.id) ? built : undefined
      },
    },
  }
}

/** Fails when a bundle of the built package also took one of the tree's sources, which would
 * then run beside the package instead of through it. */
function assertNoSources(modules: readonly string[], tree: string): void {
  const sources = `${path.join(tree, 'src')}${path.sep}`
  assert.deepEqual(
    modules.filter((module) => module.startsWith(sources)),
    [],
    "The harness bundled the tree's sources beside its built package",
  )
}

/** Fails when a bundle took a package from anywhere but this checkout's dependencies, which
 * every tree is measured with: a `node_modules` above a control could otherwise supply its own. */
function assertOwnDependencies(modules: readonly string[]): void {
  const own = `${realpathSync(path.join(ROOT, 'node_modules'))}${path.sep}`
  const foreign = modules
    .filter((module) => module.split(/[/\\]/).includes('node_modules'))
    .map((module) => realpathSync(module))
    .filter((input) => !input.startsWith(own))
  assert.deepEqual(
    foreign,
    [],
    "The harness bundled packages from outside this checkout's dependencies",
  )
}

/**
 * Bundles the tree's frozen harness, with the tool-only overlays: the diagnostic registry when
 * the scenario is not frozen, phase markers and a timer outside the measured loop, and counters
 * when it counts. The frozen workload and its warmup and measurement loops stay intact.
 */
export async function bundleHarness(options: HarnessOptions): Promise<Harness> {
  const source = path.join(options.tree, 'perf', 'profile-harness.ts')
  const original = readFileSync(source, 'utf8')
  assert.equal(original.split(MEASUREMENT).length, 2, 'Frozen harness measurement marker changed')
  const overlaid = phaseOverlay(options.overlay ? diagnosticOverlay(original, options) : original)
  const contents =
    options.counting === undefined ? overlaid : counterOverlay(overlaid, options.counting)
  const counterSites: CounterSites = {}
  mkdirSync(options.directory, { recursive: true })
  writeFileSync(path.join(options.directory, 'harness-source.ts'), contents)
  const bundlePath = path.join(options.directory, 'harness.mjs')
  const {
    output: [chunk],
  } = await build({
    input: source,
    logLevel: 'warn',
    output: { codeSplitting: false, file: bundlePath, format: 'esm', sourcemap: true },
    platform: 'node',
    // The overlaid harness stands in for the frozen one, at its path.
    plugins: [
      virtualModule(source, contents),
      ...(options.package ? [packagePlugin(options.tree)] : []),
      ...counterPlugins(options, counterSites),
    ],
    resolve: { modules: ['node_modules', path.join(ROOT, 'node_modules')] },
  })
  assertOwnDependencies(chunk.moduleIds)
  if (options.package) assertNoSources(chunk.moduleIds, options.tree)
  const map = JSON.parse(readFileSync(`${bundlePath}.map`, 'utf8')) as SourceMapPayload
  return { bundlePath, counterSites, root: options.tree, sourceMap: new SourceMap(map) }
}

/** One run of a bundled harness in a fresh Node process. */
export interface HarnessRun {
  readonly batches: number
  readonly bundle: string
  /** Where the run's output goes. */
  readonly log: string
  readonly scenario: string
  readonly warmup: number
  /** Node flags, such as V8 tracing. */
  readonly flags?: readonly string[]
  /** The sampler's mode, output path and interval, for cpu and heap profiles. */
  readonly sampler?: readonly string[]
}

/** Runs a harness in `cwd`, keeps its output in the run's log and returns what it printed; a
 * run that fails raises. */
export function runHarness(run: HarnessRun, cwd: string): string {
  const result = spawnSync(
    process.execPath,
    [
      ...(run.flags ?? []),
      run.bundle,
      run.scenario,
      String(run.batches),
      String(run.warmup),
      ...(run.sampler ?? []),
    ],
    {
      cwd,
      encoding: 'utf8',
      env: { ...process.env, NODE_NO_WARNINGS: '1' },
      maxBuffer: 50 * 1024 * 1024,
    },
  )
  writeFileSync(run.log, `${result.stdout}${result.stderr}`)
  if (result.status !== 0)
    throw new Error(
      `${run.scenario} failed (${result.error?.message ?? `exit ${String(result.status)}`}); see ${run.log}`,
    )
  return result.stdout
}

/** The JSON record a harness printed on the line that starts with `prefix`. */
export function record(output: string, prefix: string): unknown {
  const line = output.split('\n').find((candidate) => candidate.startsWith(prefix))
  assert(line !== undefined, `${prefix.trim()} record missing`)
  return JSON.parse(line.slice(prefix.length))
}
