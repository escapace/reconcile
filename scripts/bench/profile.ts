// Profiles one scenario in one tree: samples time or allocation and attributes it to source
// through the bundle's source map, or traces V8's optimizations and deoptimizations.
import { mkdirSync, writeFileSync } from 'node:fs'
import path from 'node:path'
import { entry } from '../framework/entry'
import { parseCPUProfile, parseDeopts, parseHeapProfile, type WeightedFrame } from './frames'
import { bundleHarness, runHarness, type Harness } from './harness'
import { inOverlay } from './scenarios'

/** The trace pass runs at most this many measurement batches. */
const TRACE_BATCH_LIMIT = 200

/** The configuration `pnpm bench profile` passes. */
interface Config {
  readonly batches: number
  readonly directory: string
  /** The sampling interval: microseconds for cpu, bytes for heap. */
  readonly interval: number
  readonly mode: 'cpu' | 'deopt' | 'heap'
  readonly scenario: string
  readonly size: number
  readonly tree: string
  readonly warmup: number
}

/** Frames by self weight, heaviest first. */
const bySelf = <T extends { frames: WeightedFrame[] }>(attribution: T): T => ({
  ...attribution,
  frames: attribution.frames.toSorted((left, right) => right.self - left.self),
})

/** Runs the pass and returns its result, keeping the raw profile or trace under `raw/`. */
function pass(config: Config, harness: Harness): { artifact: string; result: unknown } {
  const raw = path.join(config.directory, 'raw')
  mkdirSync(raw, { recursive: true })
  const run = {
    batches: config.batches,
    bundle: harness.bundlePath,
    log: path.join(raw, `${config.scenario}.${config.mode}.log`),
    scenario: config.scenario,
    warmup: config.warmup,
  }
  if (config.mode === 'deopt') {
    const batches = Math.min(config.batches, TRACE_BATCH_LIMIT)
    const output = runHarness(
      { ...run, batches, flags: ['--trace-opt', '--trace-deopt'] },
      config.tree,
    )
    const scope = 'Setup, warmup, measurement and completion; see phase markers in raw log.'
    return { artifact: run.log, result: { ...parseDeopts(output), scope } }
  }
  const artifact = path.join(raw, `${config.scenario}.${config.mode}profile`)
  runHarness({ ...run, sampler: [config.mode, artifact, String(config.interval)] }, config.tree)
  if (config.mode === 'heap')
    return { artifact, result: bySelf(parseHeapProfile(artifact, harness)) }
  const cpu = parseCPUProfile(artifact, harness)
  return { artifact, result: { ...cpu, attribution: bySelf(cpu.attribution) } }
}

async function main(config: Config): Promise<number> {
  const harness = await bundleHarness({
    counting: undefined,
    directory: config.directory,
    overlay: inOverlay(config.scenario),
    package: false,
    size: config.size,
    tree: config.tree,
  })
  const { artifact, result } = pass(config, harness)
  const summary = { artifact, mode: config.mode, result }
  writeFileSync(
    path.join(config.directory, 'summary.json'),
    `${JSON.stringify(summary, undefined, 2)}\n`,
  )
  console.log(JSON.stringify(summary, undefined, 2))
  return 0
}

await entry(import.meta.filename, main)
