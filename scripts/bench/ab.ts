// An alternating A/B timing round over frozen harness bundles. It bundles each tree's harness,
// once for the frozen scenarios and once for the rest, runs every scenario for a few batches,
// sizes each scenario's batches (about `seconds` of measured work per process by default) and
// stops if the round would not fit its budget. It then registers the design (scenarios, pairs,
// batches, size, bundle hashes, Node version, tree commits and sources, frozen and shared
// workload hashes) before any sample is taken, and alternates the order of the tree and the
// control per pair, in fresh Node processes. Every completed sample is kept at once. Each scenario
// reports the median paired change (negative is faster), a bootstrap 90% interval from 10 pairs
// on, the count of faster pairs, a reading and the seconds each process measured. With
// `package`, each tree's workloads run its built package instead of its sources.
import { createHash } from 'node:crypto'
import { readFileSync, writeFileSync } from 'node:fs'
import path from 'node:path'
import { entry } from '../framework/entry'
import { writeJson } from '../framework/files'
import { bundleHarness, record, runHarness } from './harness'
import { frozenHash, gitState, packageHash, sharedHash, sourceHash } from './provenance'
import { inOverlay } from './scenarios'
import {
  batchCounts,
  type Counts,
  estimateSeconds,
  GAIN_PERCENT,
  GUARD_PERCENT,
  interval,
  median,
  PREFLIGHT,
  reading,
  type Reading,
  type Sample,
} from './stats'

/** The trees of a round, the measured tree first. */
const LABELS = ['tree', 'control'] as const
export type Label = (typeof LABELS)[number]

/** The share of the remaining budget a round's estimate may take: it has run up to 7% short. */
const ESTIMATE_MARGIN = 1.15
/** Seconds of the budget kept for the summary and shutdown. */
const RESERVE_SECONDS = 10

/** The configuration `pnpm bench ab` passes. */
export interface Config {
  readonly batches: number | 'auto'
  /** The control's source tree. */
  readonly control: string
  readonly directory: string
  /** default, small, deciding or custom: which rule of the protocol the round serves; a round
   * of two trees with the same sources is recorded as `aa`. */
  readonly kind: string
  /** Times each tree's built package, which the round builds first, instead of its sources. */
  readonly package: boolean
  readonly pairs: number
  readonly scenarios: readonly string[]
  readonly seconds: number
  readonly size: number
  readonly tree: string
  readonly warmup: number | 'auto'
}

/** One scenario's result, as `summary.json` records it. */
export interface ScenarioSummary {
  readonly controlMedianUsPerOperation: number
  readonly fasterPairs: number
  readonly medianPairedPercentChange: number
  readonly medianPairedPercentInterval: [number, number] | null
  readonly pairedPercentChanges: number[]
  readonly reading: Reading
  readonly treeMedianUsPerOperation: number
  /** The median seconds each tree's processes measured, which a round sizes to about the
   * seconds it was asked for. */
  readonly medianMeasuredSeconds?: Readonly<Record<Label, number>>
}

/** One timed run, as `samples.json` records it. */
export interface Row extends Sample {
  readonly label: Label
  readonly operations: number
  readonly pair: number
}

const sha256 = (data: string | Buffer): string => createHash('sha256').update(data).digest('hex')

/** What the round measures: each tree's sources and frozen workloads, the shared workloads and,
 * when it times the built packages, each tree's package. */
function provenanceOf(config: Config) {
  return {
    frozen: { control: frozenHash(config.control), tree: frozenHash(config.tree) },
    packages: config.package
      ? { control: packageHash(config.control), tree: packageHash(config.tree) }
      : null,
    shared: sharedHash(),
    sources: { control: sourceHash(config.control), tree: sourceHash(config.tree) },
  }
}

type Provenance = ReturnType<typeof provenanceOf>

/** One timed run of a scenario in a fresh process. */
function measure(bundle: string, scenario: string, counts: Counts, log: string, tree: string) {
  const started = performance.now()
  const output = runHarness({ ...counts, bundle, log, scenario }, tree)
  const wallSeconds = (performance.now() - started) / 1000
  const time = record(output, 'RECONCILE_TIME ') as { elapsedMs: number; operations: number }
  return { scenario, wallSeconds, ...time }
}

/** Each tree's bundle per scenario: one for the frozen scenarios, one for the overlay. */
async function bundles(config: Config): Promise<Record<Label, Record<string, string>>> {
  const result: Record<Label, Record<string, string>> = { control: {}, tree: {} }
  for (const label of LABELS) {
    const shared = new Map<boolean, string>()
    for (const scenario of config.scenarios) {
      const overlay = inOverlay(scenario)
      let bundle = shared.get(overlay)
      if (bundle === undefined) {
        const harness = await bundleHarness({
          counting: undefined,
          directory: path.join(config.directory, 'bundles', label, overlay ? 'overlay' : 'frozen'),
          overlay,
          package: config.package,
          size: config.size,
          tree: config[label],
        })
        bundle = harness.bundlePath
        shared.set(overlay, bundle)
      }
      result[label][scenario] = bundle
    }
  }
  return result
}

const signed = (value: number): string => `${value >= 0 ? '+' : ''}${value.toFixed(2)}`

/** One scenario's summary from the round's rows; each tree's time per operation is its own. */
export function summarize(rows: readonly Row[], scenario: string): ScenarioSummary {
  const samples = rows.filter((row) => row.scenario === scenario)
  const of = (label: Label): Row[] => samples.filter((row) => row.label === label)
  const elapsed = (label: Label): number[] => of(label).map((row) => row.elapsedMs)
  const perOperation = (label: Label): number =>
    (median(elapsed(label)) * 1000) / of(label)[0].operations
  const tree = elapsed('tree')
  const control = elapsed('control')
  const changes = tree.map((value, index) => 100 * (value / control[index] - 1))
  const bounds = interval(changes)
  const change = median(changes)
  return {
    controlMedianUsPerOperation: perOperation('control'),
    fasterPairs: changes.filter((value) => value < 0).length,
    medianMeasuredSeconds: { control: median(control) / 1000, tree: median(tree) / 1000 },
    medianPairedPercentChange: change,
    medianPairedPercentInterval: bounds ?? null,
    pairedPercentChanges: changes,
    reading: reading(change, bounds),
    treeMedianUsPerOperation: perOperation('tree'),
  }
}

/** The round's table, as `report.md` and the console show it. */
function table(summary: Readonly<Record<string, ScenarioSummary>>): string {
  const lines = [
    '| Workload | Control median µs/op | Tree median µs/op | Median paired change | 90% interval | Faster pairs | Reading |',
    '| --- | ---: | ---: | ---: | ---: | ---: | --- |',
  ]
  for (const [scenario, entry] of Object.entries(summary)) {
    const bounds = entry.medianPairedPercentInterval
    const shown = bounds === null ? 'n/a' : `[${signed(bounds[0])}%, ${signed(bounds[1])}%]`
    lines.push(
      `| ${scenario} | ${entry.controlMedianUsPerOperation.toFixed(2)} | ` +
        `${entry.treeMedianUsPerOperation.toFixed(2)} | ${signed(entry.medianPairedPercentChange)}% | ` +
        `${shown} | ${entry.fasterPairs}/${entry.pairedPercentChanges.length} | ${entry.reading} |`,
    )
  }
  return lines.join('\n')
}

/** Writes the design of the round before any sample is taken. */
function writePlan(
  config: Config,
  paths: Record<Label, Record<string, string>>,
  counts: Record<string, Counts>,
  estimate: number,
  { frozen, packages, shared, sources }: Provenance,
): void {
  // Two trees that time the same thing only measure noise.
  const same =
    packages === null ? sources.control === sources.tree : packages.control === packages.tree
  const perLabel = <T>(read: (label: Label) => T): Record<Label, T> => ({
    control: read('control'),
    tree: read('tree'),
  })
  writeJson(path.join(config.directory, 'plan.json'), {
    batches: counts,
    bundles: paths,
    estimatedSamplingSeconds: estimate,
    frozenWorkloadSha256: frozen,
    git: perLabel((label) => gitState(config[label])),
    kind: same ? 'aa' : config.kind,
    library: packages === null ? 'sources' : 'package',
    node: process.version,
    packageSha256: packages,
    pairs: config.pairs,
    requestedSecondsPerProcess: config.seconds,
    roots: perLabel((label) => config[label]),
    scenarios: config.scenarios,
    sha256: perLabel((label) =>
      Object.fromEntries(
        Object.entries(paths[label]).map(([scenario, file]) => [
          scenario,
          sha256(readFileSync(file)),
        ]),
      ),
    ),
    // The serialization and small workloads and the diagnostics come from this checkout for both
    // trees.
    sharedWorkloadSha256: shared,
    size: config.size,
    sourceSha256: sources,
  })
}

/** Samples every pair, alternating which tree runs first, and keeps each sample at once. */
function sample(
  config: Config,
  paths: Record<Label, Record<string, string>>,
  counts: Record<string, Counts>,
): Row[] {
  const rows: Row[] = []
  for (let pair = 0; pair < config.pairs; pair += 1) {
    const order = pair % 2 === 0 ? LABELS : LABELS.toReversed()
    for (const scenario of config.scenarios)
      for (const label of order) {
        const log = path.join(config.directory, `${pair}-${scenario}-${label}.log`)
        const run = measure(paths[label][scenario], scenario, counts[scenario], log, config[label])
        rows.push({ label, pair, ...run })
        writeJson(path.join(config.directory, 'samples.json'), rows)
      }
    console.log(`Completed pair ${pair + 1}/${config.pairs}`)
  }
  return rows
}

async function main(config: Config): Promise<number> {
  // The round's deadline is wall-clock time; the rest of the round measures with a monotonic clock.
  const budgetMs = Number(process.env.RECONCILE_DEADLINE) - Date.now()
  if (!Number.isFinite(budgetMs))
    throw new Error('RECONCILE_DEADLINE is not set; run `pnpm bench ab`')
  const started = performance.now()
  // The hashes describe what is bundled only when nothing changes while it is bundled.
  const provenance = provenanceOf(config)
  const paths = await bundles(config)
  // One short run of every bundle, so a tree that lacks a scenario fails before any sample.
  const preflight = LABELS.flatMap((label) =>
    config.scenarios.map((scenario) =>
      measure(
        paths[label][scenario],
        scenario,
        PREFLIGHT,
        path.join(config.directory, `preflight-${scenario}-${label}.log`),
        config[label],
      ),
    ),
  )
  const counts = batchCounts(preflight, config.batches, config.warmup, config.seconds)
  const estimate = estimateSeconds(preflight, config.pairs, counts)
  const remaining = (budgetMs - (performance.now() - started)) / 1000 - RESERVE_SECONDS
  if (estimate * ESTIMATE_MARGIN > remaining) {
    console.error(
      `The round needs about ${estimate.toFixed(0)} s of sampling but ${remaining.toFixed(0)} s ` +
        'remain in the budget; select fewer scenarios, pairs or batches.',
    )
    return 1
  }
  if (JSON.stringify(provenanceOf(config)) !== JSON.stringify(provenance)) {
    console.error(
      'The sources, packages or workloads changed while the round bundled them, so the bundles may not be ' +
        'what the hashes describe; rerun the round.',
    )
    return 1
  }
  writePlan(config, paths, counts, estimate, provenance)
  const rows = sample(config, paths, counts)
  const summary = Object.fromEntries(
    config.scenarios.map((scenario) => [scenario, summarize(rows, scenario)]),
  )
  const report = table(summary)
  writeFileSync(
    path.join(config.directory, 'report.md'),
    '# Alternating A/B timing round\n\nNegative changes mean the tree is faster than the control. ' +
      'Medians of paired whole-process loop latency; no cumulative or general speedup is inferred. ' +
      `A reading is faster when the interval is below zero and the median gains at least ${GAIN_PERCENT}%, ` +
      `slower when the interval is above zero and the median exceeds the ${GUARD_PERCENT}% guard, and ` +
      'slightly faster or slower when the interval excludes zero within those limits. Keeping a ' +
      `change needs two deciding rounds that read faster.\n\n${report}\n`,
  )
  // The summary marks the round complete, so it is written last.
  writeJson(path.join(config.directory, 'summary.json'), summary)
  console.log(report)
  console.log('Negative is faster. Keeping a change needs two deciding rounds that read faster.')
  return 0
}

await entry(import.meta.filename, main)
