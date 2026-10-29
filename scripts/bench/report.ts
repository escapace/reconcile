// Reads an experiment's A/B rounds and states, for the sources measured and for the built package
// measured, each workload's readings against the control, what the acceptance rule concludes and
// which rounds are missing. Only rounds that measured the same things are judged together: a
// round must have passed, measured the control as the experiment pinned it, and run the same
// frozen workloads in both trees; a diagnostic's readings combine only across rounds of the same
// shared workloads and size, and rounds that timed built packages only with each other.
import { readFileSync } from 'node:fs'
import path from 'node:path'
import { ROOT } from '../framework/paths'
import type { ScenarioSummary } from './ab'
import { pinnedSource, roundsOf, type Experiment } from './experiments'
import { sourceHash } from './provenance'
import { inOverlay } from './scenarios'
import type { Reading } from './stats'

/** An A/B round of the experiment, as its plan and summary record it. */
export interface AbRound {
  /** `aa` when both trees held the same sources, else the rule the round served. */
  readonly kind: string
  readonly name: string
  /** The measured tree's sources, or its built package when the round timed packages. */
  readonly source: string
  readonly summary: Readonly<Record<string, ScenarioSummary>>
  /** The control's sources. */
  readonly control?: string
  /** The control's built package, when the round timed packages. */
  readonly controlPackage?: string
  /** Whether the round timed the trees' sources or their built packages. */
  readonly library?: Library
  /** Whether both trees ran the same frozen workloads. */
  readonly sameFrozen?: boolean
  /** The shared workloads and diagnostic size, which a diagnostic's readings depend on. */
  readonly workloads?: string
}

/** What an A/B round timed: the trees' sources, or their built packages. */
export type Library = 'package' | 'sources'

interface Pair {
  readonly control: string
  readonly tree: string
}

interface Plan {
  readonly kind: string
  readonly sourceSha256: Pair
  /** The built packages, in a round that timed them. */
  readonly frozenWorkloadSha256?: { readonly control: string; readonly tree: string }
  readonly packageSha256?: Pair | null
  readonly sharedWorkloadSha256?: string
  readonly size?: number
}

/** A JSON file of a round, or undefined when it is missing or cannot be read. */
function readJson<T>(directory: string, file: string): T | undefined {
  try {
    return JSON.parse(readFileSync(path.join(directory, file), 'utf8')) as T
  } catch {
    return undefined
  }
}

const passed = (directory: string): boolean =>
  readJson<{ status?: string }>(directory, 'receipt.json')?.status === 'passed'

/** The shared workloads and diagnostic size a round ran, as far as its plan records them. */
const workloadsOf = (plan: Plan): string =>
  `${plan.sharedWorkloadSha256 ?? 'unrecorded'}:${plan.size ?? 'unrecorded'}`

/** The round that a passed A/B round's plan and summary record. */
function roundOf(name: string, plan: Plan, summary: Record<string, ScenarioSummary>): AbRound {
  const sources = plan.sourceSha256
  const packages = plan.packageSha256 ?? undefined
  // A round that timed packages measured them, whatever their sources.
  const timed = packages ?? sources
  const frozen = plan.frozenWorkloadSha256
  return {
    control: sources.control,
    controlPackage: packages?.control,
    // Rounds recorded before the A/A check kept the kind they were asked for.
    kind: timed.control === timed.tree ? 'aa' : plan.kind,
    library: packages === undefined ? 'sources' : 'package',
    name,
    sameFrozen: frozen === undefined || frozen.control === frozen.tree,
    source: timed.tree,
    summary,
    workloads: workloadsOf(plan),
  }
}

/** The experiment's A/B rounds that passed and summarized, oldest first. */
function abRounds(experiment: Experiment): AbRound[] {
  return roundsOf(experiment).flatMap((directory) => {
    const plan = readJson<Plan>(directory, 'plan.json')
    const summary = readJson<Record<string, ScenarioSummary>>(directory, 'summary.json')
    if (plan === undefined || summary === undefined || !passed(directory)) return []
    return [roundOf(path.basename(directory), plan, summary)]
  })
}

/** Whether the experiment holds a size comparison of these sources, or of this built package,
 * against its control. */
const hasSizes = (experiment: Experiment, source: string, library: Library): boolean =>
  roundsOf(experiment).some((directory) => {
    const plan = readJson<{
      modules: unknown
      sourceSha256: { control: string | null; tree: string }
      packageSha256?: { tree: string } | null
    }>(directory, 'plan.json')
    const measured = library === 'package' ? plan?.packageSha256?.tree : plan?.sourceSha256.tree
    return (
      plan?.modules === null &&
      measured === source &&
      plan.sourceSha256.control === pinnedSource(experiment) &&
      passed(directory)
    )
  })

const readingsOf = (
  rounds: readonly AbRound[],
  scenario: string,
  kinds: readonly string[],
): Reading[] =>
  rounds.flatMap((round) =>
    kinds.includes(round.kind) && scenario in round.summary
      ? [round.summary[scenario].reading]
      : [],
  )

const slower = (reading: Reading): boolean => reading === 'slower' || reading === 'slightly slower'

const count = (number: number, noun: string): string =>
  `${number} ${noun}${number === 1 ? '' : 's'}`

/** What the rule concludes from deciding rounds none of which reads slower. */
function undecided(deciding: readonly Reading[]): string {
  const faster = deciding.filter((reading) => reading === 'faster').length
  const slightly = deciding.filter((reading) => reading === 'slightly slower').length
  const within = slightly === 0 ? '' : `, ${slightly} slightly slower within the guard`
  return (
    `not rejected: no deciding round reads slower (${count(deciding.length, 'deciding round')}, ` +
    `${faster} faster${within}); keeping it as the target needs two or more, every one faster`
  )
}

/**
 * What the protocol concludes for one workload. A deciding round that reads slower rejects the
 * change. As the change's target, a workload keeps it only when it has two deciding rounds or
 * more and every one reads faster. As a guard, a workload whose default, small or custom round
 * reads slower or slightly slower needs a deciding round of its own; rounds with too few pairs
 * to read show nothing.
 */
export function verdict(rounds: readonly AbRound[], scenario: string): string {
  const deciding = readingsOf(rounds, scenario, ['deciding'])
  if (deciding.includes('slower')) return 'rejected: a deciding round reads slower'
  if (deciding.length >= 2 && deciding.every((reading) => reading === 'faster'))
    return 'faster: two deciding rounds or more, every one faster'
  if (deciding.length > 0) return undecided(deciding)
  const guards = readingsOf(rounds, scenario, ['default', 'small', 'custom'])
  if (guards.some(slower)) return 'needs a deciding round: a guard round reads slower'
  if (guards.every((reading) => reading === 'too few pairs'))
    return 'no evidence: its rounds have too few pairs to read'
  return 'no round reads slower'
}

const shown = (entry: ScenarioSummary): string =>
  `${entry.reading} ${entry.medianPairedPercentChange >= 0 ? '+' : ''}${entry.medianPairedPercentChange.toFixed(2)}%`

/** The rounds whose readings of `scenario` combine: for a diagnostic, those of the workloads and
 * size its latest round ran, which the label then names when other rounds ran others. */
function comparable(
  rounds: readonly AbRound[],
  scenario: string,
): { label: string; rounds: AbRound[] } {
  const measuring = rounds.filter((round) => scenario in round.summary)
  const latest = measuring.at(-1)?.workloads
  if (!inOverlay(scenario) || measuring.every((round) => round.workloads === latest))
    return { label: scenario, rounds: measuring }
  const [, size = '?'] = latest?.split(':') ?? []
  return {
    label: `${scenario} (size ${size}, its latest workloads)`,
    rounds: measuring.filter((round) => round.workloads === latest),
  }
}

/** The verdict of each workload measured in `rounds`, with its readings. */
function verdicts(rounds: readonly AbRound[]): string[] {
  const scenarios = [...new Set(rounds.flatMap((round) => Object.keys(round.summary)))]
  const rows = scenarios.map((scenario) => ({ scenario, ...comparable(rounds, scenario) }))
  const width = Math.max(...rows.map(({ label }) => label.length)) + 2
  return rows.map(({ label, rounds: combined, scenario }) => {
    const readings = combined.map((round) => `${round.kind} ${shown(round.summary[scenario])}`)
    return `  ${label.padEnd(width)}${verdict(combined, scenario)}: ${readings.join(', ')}`
  })
}

/** The note on the rounds that the protocol asks for and that `rounds`, all of `library`,
 * lack; none when they lack none. */
function missing(
  rounds: readonly AbRound[],
  experiment: Experiment,
  source: string,
  library: Library,
): string[] {
  const what = library === 'package' ? 'this package' : 'these sources'
  const absent = [
    ...(['default', 'small'] as const)
      .filter((kind) => !rounds.some((round) => round.kind === kind))
      .map((kind) => `a ${kind} round`),
    ...(hasSizes(experiment, source, library) ? [] : [`a size comparison of ${what}`]),
  ]
  return absent.length === 0 ? [] : ['', `Missing: ${absent.join(', ')}.`]
}

/** The sources to judge: this checkout's when a round measured them, else the latest measured. */
const judgedSource = (measured: readonly AbRound[], checkout: string): string | undefined =>
  measured.some((round) => round.source === checkout) ? checkout : measured.at(-1)?.source

function headline({ name, record }: Experiment): string {
  const changes = record.worktree ? ' with uncommitted changes' : ''
  return `Experiment ${name}: control ${record.commit.slice(0, 12)}${changes}, frozen ${record.created}.`
}

/** The notes on rounds that are not judged, and why. */
function notes(rounds: readonly AbRound[], pinned: string): string[] {
  const otherControl = rounds.filter((round) => round.control !== pinned).length
  const otherWorkloads = rounds.filter(
    (round) => round.control === pinned && round.sameFrozen === false,
  ).length
  const aa = rounds.filter(
    (round) => round.control === pinned && round.sameFrozen !== false && round.kind === 'aa',
  ).length
  return [
    ...(aa === 0 ? [] : [`${count(aa, 'A/A round')} ${aa === 1 ? 'measures' : 'measure'} noise.`]),
    ...(otherControl === 0
      ? []
      : [
          `${count(otherControl, 'round')} against another control than the one frozen, not judged.`,
        ]),
    ...(otherWorkloads === 0
      ? []
      : [
          `${count(otherWorkloads, 'round')} whose trees ran different frozen workloads, not judged.`,
        ]),
  ]
}

const roundsCount = (rounds: number): string =>
  rounds === 1 ? 'the round' : `the ${rounds} rounds`

/** The verdicts on the sources judged: this checkout's when a round measured them, else the
 * latest measured. */
function sourceVerdicts(experiment: Experiment, measured: readonly AbRound[]): string[] {
  const checkout = sourceHash(ROOT)
  const source = judgedSource(measured, checkout)
  if (source === undefined) return []
  const current = measured.filter((round) => round.source === source)
  const sources =
    source === checkout
      ? "this checkout's sources"
      : `sources ${source.slice(0, 12)}, not this checkout's`
  return [
    '',
    `Verdicts from ${roundsCount(current.length)} of ${sources}, each with its readings, oldest first:`,
    ...verdicts(current),
    ...missing(current, experiment, source, 'sources'),
  ]
}

/** The verdicts on the latest built package measured, against the same build of the control. */
function packageVerdicts(experiment: Experiment, measured: readonly AbRound[]): string[] {
  const latest = measured.at(-1)
  if (latest === undefined) return []
  const current = measured.filter(
    (round) => round.source === latest.source && round.controlPackage === latest.controlPackage,
  )
  return [
    '',
    `Verdicts from ${roundsCount(current.length)} of the built package ${latest.source.slice(0, 12)}, ` +
      `against the control's ${latest.controlPackage?.slice(0, 12)}, each with its readings, oldest first:`,
    ...verdicts(current),
    ...missing(current, experiment, latest.source, 'package'),
  ]
}

/**
 * The report of an experiment, as `pnpm bench report` prints it. It judges the rounds that
 * measured this checkout's sources, or else the latest measured sources, and apart from them the
 * rounds that timed the latest built package measured; A/A rounds, which measure noise, and
 * rounds that measured something else are counted apart.
 */
export function report(experiment: Experiment): string {
  const pinned = pinnedSource(experiment)
  const rounds = abRounds(experiment)
  const judged = rounds.filter(
    (round) => round.control === pinned && round.sameFrozen !== false && round.kind !== 'aa',
  )
  const sections = [
    ...sourceVerdicts(
      experiment,
      judged.filter((round) => round.library !== 'package'),
    ),
    ...packageVerdicts(
      experiment,
      judged.filter((round) => round.library === 'package'),
    ),
  ]
  const lines = [headline(experiment), ...notes(rounds, pinned), ...sections]
  if (sections.length === 0)
    lines.push('No A/B round of a change yet: `pnpm bench ab default --control <experiment>`.')
  return lines.join('\n')
}
