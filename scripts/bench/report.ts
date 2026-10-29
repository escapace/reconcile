// Reads an experiment's A/B rounds and states, for the sources measured, each workload's
// readings against the control, what the acceptance rule concludes and which rounds are missing.
import { existsSync, readFileSync } from 'node:fs'
import path from 'node:path'
import { ROOT } from '../framework/paths'
import { sourceHash, type ScenarioSummary } from './ab'
import { roundsOf, type Experiment } from './experiments'
import type { Reading } from './stats'

/** An A/B round of the experiment, as its plan and summary record it. */
export interface AbRound {
  readonly kind: string
  readonly name: string
  /** The measured tree's sources. */
  readonly source: string
  readonly summary: Readonly<Record<string, ScenarioSummary>>
}

const readJson = <T>(file: string): T => JSON.parse(readFileSync(file, 'utf8')) as T

/** The experiment's A/B rounds that completed, oldest first. */
function abRounds(experiment: Experiment): AbRound[] {
  return roundsOf(experiment)
    .filter((directory) => existsSync(path.join(directory, 'summary.json')))
    .map((directory) => {
      const plan = readJson<{ kind: string; sourceSha256: { tree: string } }>(
        path.join(directory, 'plan.json'),
      )
      return {
        kind: plan.kind,
        name: path.basename(directory),
        source: plan.sourceSha256.tree,
        summary: readJson<Record<string, ScenarioSummary>>(path.join(directory, 'summary.json')),
      }
    })
}

/** Whether the experiment holds a completed size comparison. */
const hasSizes = (experiment: Experiment): boolean =>
  roundsOf(experiment).some((directory) =>
    existsSync(path.join(directory, 'control', 'sizes.json')),
  )

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

/**
 * What the protocol concludes for one workload. A deciding round that reads slower rejects the
 * change. As the change's target, a workload keeps it only when it has two deciding rounds or
 * more and every one reads faster. As a guard, a workload whose default, small or custom round
 * reads slower or slightly slower needs a deciding round of its own.
 */
export function verdict(rounds: readonly AbRound[], scenario: string): string {
  const deciding = readingsOf(rounds, scenario, ['deciding'])
  if (deciding.includes('slower')) return 'rejected: a deciding round reads slower'
  if (deciding.length >= 2 && deciding.every((reading) => reading === 'faster'))
    return 'faster: every deciding round, two or more, reads faster'
  if (deciding.length > 0)
    return 'no loss; as the target it needs two deciding rounds or more, every one faster'
  if (readingsOf(rounds, scenario, ['default', 'small', 'custom']).some(slower))
    return 'needs a deciding round: a guard round reads slower'
  return 'no loss in its rounds'
}

const shown = (entry: ScenarioSummary): string =>
  `${entry.reading} ${entry.medianPairedPercentChange >= 0 ? '+' : ''}${entry.medianPairedPercentChange.toFixed(2)}%`

/** The verdict of each workload measured in `rounds`, with its readings. */
function verdicts(rounds: readonly AbRound[]): string[] {
  const scenarios = [...new Set(rounds.flatMap((round) => Object.keys(round.summary)))]
  const width = Math.max(...scenarios.map((scenario) => scenario.length)) + 2
  return scenarios.map((scenario) => {
    const readings = rounds.flatMap((round) =>
      scenario in round.summary ? [`${round.kind} ${shown(round.summary[scenario])}`] : [],
    )
    return `  ${scenario.padEnd(width)}${verdict(rounds, scenario)}: ${readings.join(', ')}`
  })
}

/** The rounds that the protocol asks for and that `rounds` lack. */
function missing(rounds: readonly AbRound[], experiment: Experiment): string[] {
  return [
    ...(['default', 'small'] as const)
      .filter((kind) => !rounds.some((round) => round.kind === kind))
      .map((kind) => `a ${kind} round`),
    ...(hasSizes(experiment) ? [] : ['a size comparison']),
  ]
}

/** The sources to judge: this checkout's when a round measured them, else the latest measured. */
const judgedSource = (measured: readonly AbRound[], checkout: string): string | undefined =>
  measured.some((round) => round.source === checkout) ? checkout : measured.at(-1)?.source

function headline({ name, record }: Experiment): string {
  const changes = record.worktree ? ' with uncommitted changes' : ''
  return `Experiment ${name}: control ${record.commit.slice(0, 12)}${changes}, frozen ${record.created}.`
}

const noise = (count: number): string[] =>
  count === 0 ? [] : [`${count} A/A ${count === 1 ? 'round measures' : 'rounds measure'} noise.`]

function verdictsHeading(count: number, source: string, checkout: string): string {
  const rounds = count === 1 ? 'the round' : `the ${count} rounds`
  const sources =
    source === checkout
      ? "this checkout's sources"
      : `sources ${source.slice(0, 12)}, not this checkout's`
  return `Verdicts from ${rounds} of ${sources}, each with its readings, oldest first:`
}

/**
 * The report of an experiment, as `pnpm bench report` prints it. It judges the rounds that
 * measured this checkout's sources, or else the latest measured sources; A/A rounds, which
 * measure noise, are counted apart.
 */
export function report(experiment: Experiment): string {
  const rounds = abRounds(experiment)
  const measured = rounds.filter((round) => round.kind !== 'aa')
  const checkout = sourceHash(ROOT)
  const source = judgedSource(measured, checkout)
  const lines = [headline(experiment), ...noise(rounds.length - measured.length)]
  if (source === undefined)
    return [
      ...lines,
      'No A/B round of a change yet: `pnpm bench ab default --control <experiment>`.',
    ].join('\n')
  const current = measured.filter((round) => round.source === source)
  lines.push('', verdictsHeading(current.length, source, checkout), ...verdicts(current))
  const absent = missing(current, experiment)
  if (absent.length > 0) lines.push('', `Missing: ${absent.join(', ')}.`)
  return lines.join('\n')
}
