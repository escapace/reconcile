// An alternating A/B timing round over frozen harness bundles. It bundles each tree's harness,
// once for the frozen scenarios and once for the rest, runs every scenario for a few batches,
// sizes each scenario's batches (about `seconds` of measured work per process by default) and
// stops if the round would not fit its budget. It then registers the design (scenarios, pairs,
// batches, size, bundle hashes, Node version, tree commits and sources, frozen workload hashes)
// before any sample is taken, and alternates the order of the tree and the control per pair, in
// fresh Node processes. Every completed sample is kept at once. Each scenario reports the median
// paired change (negative is faster), a bootstrap 90% interval from 10 pairs on, the count of
// faster pairs and a reading.
import { spawnSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { existsSync, readdirSync, readFileSync, writeFileSync } from 'node:fs'
import path from 'node:path'
import { entry } from '../framework/entry'
import { ROOT } from '../framework/paths'
import { bundleHarness, record, runHarness } from './harness'
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
}

/** One timed run, as `samples.json` records it. */
export interface Row extends Sample {
  readonly label: Label
  readonly operations: number
  readonly pair: number
}

const sha256 = (data: string | Buffer): string => createHash('sha256').update(data).digest('hex')

/** A hash of the tree's library sources, which tells two rounds on the same code apart from
 * rounds on changed code. */
export function sourceHash(tree: string): string {
  const files = readdirSync(path.join(tree, 'src'), { recursive: true, withFileTypes: true })
    .filter((file) => file.isFile() && !file.parentPath.includes('__tests__'))
    .map((file) => path.relative(tree, path.join(file.parentPath, file.name)))
    .toSorted()
  return sha256(
    files.map((file) => `${file}\0${sha256(readFileSync(path.join(tree, file)))}`).join('\n'),
  )
}

/** A hash of the frozen workload files, which both trees must share. */
function frozenHash(tree: string): string {
  const hash = createHash('sha256')
  for (const name of ['perf/scenarios.ts', 'perf/config.ts', 'perf/profile-harness.ts']) {
    const file = path.join(tree, name)
    hash.update(existsSync(file) ? readFileSync(file) : 'missing')
  }
  return hash.digest('hex')
}

/** The commit and whether the tree has uncommitted changes, or null outside git. */
function gitState(tree: string): { commit: string; dirty: boolean } | null {
  const head = spawnSync('git', ['-C', tree, 'rev-parse', 'HEAD'], { encoding: 'utf8' })
  if (head.status !== 0) return null
  const status = spawnSync('git', ['-C', tree, 'status', '--porcelain'], { encoding: 'utf8' })
  return { commit: head.stdout.trim(), dirty: status.stdout.trim() !== '' }
}

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

/** One scenario's summary from the round's rows. */
export function summarize(rows: readonly Row[], scenario: string): ScenarioSummary {
  const samples = rows.filter((row) => row.scenario === scenario)
  const elapsed = (label: Label): number[] =>
    samples.filter((row) => row.label === label).map((row) => row.elapsedMs)
  const tree = elapsed('tree')
  const control = elapsed('control')
  const { operations } = samples[0]
  const changes = tree.map((value, index) => 100 * (value / control[index] - 1))
  const bounds = interval(changes)
  const change = median(changes)
  return {
    controlMedianUsPerOperation: (median(control) * 1000) / operations,
    fasterPairs: changes.filter((value) => value < 0).length,
    medianPairedPercentChange: change,
    medianPairedPercentInterval: bounds ?? null,
    pairedPercentChanges: changes,
    reading: reading(change, bounds),
    treeMedianUsPerOperation: (median(tree) * 1000) / operations,
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

const json = (value: unknown): string => `${JSON.stringify(value, undefined, 2)}\n`

/** Writes the design of the round before any sample is taken. */
function writePlan(
  config: Config,
  paths: Record<Label, Record<string, string>>,
  counts: Record<string, Counts>,
  estimate: number,
): void {
  const frozen = { control: frozenHash(config.control), tree: frozenHash(config.tree) }
  if (frozen.control !== frozen.tree)
    console.log("Warning: the trees' perf/ workloads differ, so the scenarios are not the same.")
  const perLabel = <T>(read: (label: Label) => T): Record<Label, T> => ({
    control: read('control'),
    tree: read('tree'),
  })
  const sources = perLabel((label) => sourceHash(config[label]))
  const plan = {
    batches: counts,
    bundles: paths,
    estimatedSamplingSeconds: estimate,
    frozenWorkloadSha256: frozen,
    git: perLabel((label) => gitState(config[label])),
    // A round of two trees with the same sources only measures noise.
    kind: sources.control === sources.tree ? 'aa' : config.kind,
    measuredSecondsPerProcess: config.seconds,
    node: process.version,
    pairs: config.pairs,
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
    // The serialization and small workloads come from this checkout for both trees.
    sharedWorkloadSha256: sha256(readFileSync(path.join(ROOT, 'scripts', 'bench-workloads.ts'))),
    size: config.size,
    sourceSha256: sources,
  }
  writeFileSync(path.join(config.directory, 'plan.json'), json(plan))
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
        writeFileSync(path.join(config.directory, 'samples.json'), json(rows))
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
  writePlan(config, paths, counts, estimate)
  const rows = sample(config, paths, counts)
  const summary = Object.fromEntries(
    config.scenarios.map((scenario) => [scenario, summarize(rows, scenario)]),
  )
  writeFileSync(path.join(config.directory, 'summary.json'), json(summary))
  const report = table(summary)
  writeFileSync(
    path.join(config.directory, 'report.md'),
    '# Alternating A/B timing round\n\nNegative changes mean the tree is faster than the control. ' +
      'Medians of paired whole-process loop latency; no cumulative or general speedup is inferred. ' +
      `A reading is faster when the interval is below zero and the median gains at least ${GAIN_PERCENT}%, ` +
      `slower when the interval is above zero and the median exceeds the ${GUARD_PERCENT}% guard, and ` +
      'slightly faster or slower when the interval excludes zero within those limits. Keeping a ' +
      `change needs two independent faster rounds.\n\n${report}\n`,
  )
  console.log(report)
  console.log('Negative is faster. Keeping a change needs two independent rounds that read faster.')
  return 0
}

await entry(import.meta.filename, main)
