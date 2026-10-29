// Reads an experiment's A/B rounds and states, for the tree's latest sources, each workload's
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

/**
 * What the protocol concludes for one workload: a deciding round that reads slower rejects the
 * tree, two deciding rounds that read faster keep it, and a guard round (default, small or
 * custom) that reads slower or slightly slower needs a deciding round of the workload's own.
 */
export function verdict(rounds: readonly AbRound[], scenario: string): string {
  const deciding = readingsOf(rounds, scenario, ['deciding'])
  const faster = deciding.filter((reading) => reading === 'faster').length
  if (deciding.includes('slower')) return 'rejected: a deciding round reads slower'
  if (faster >= 2) return 'meets the acceptance rule: two deciding rounds read faster'
  if (deciding.length > 0)
    return `${faster} of ${deciding.length} deciding rounds read faster; keeping a change needs two`
  const guard = readingsOf(rounds, scenario, ['default', 'small', 'custom'])
  if (guard.some((reading) => reading === 'slower' || reading === 'slightly slower'))
    return 'needs a deciding round: a guard round reads slower'
  return 'no loss in its rounds'
}

const shown = (entry: ScenarioSummary): string =>
  `${entry.reading} ${entry.medianPairedPercentChange >= 0 ? '+' : ''}${entry.medianPairedPercentChange.toFixed(2)}%`

/** The report of an experiment, as `pnpm bench report` prints it. */
export function report(experiment: Experiment): string {
  const { record } = experiment
  const lines = [
    `Experiment ${experiment.name}: control ${record.commit.slice(0, 12)}` +
      `${record.worktree ? ' with uncommitted changes' : ''}, frozen ${record.created}.`,
  ]
  const rounds = abRounds(experiment)
  const latest = rounds.at(-1)
  if (latest === undefined)
    return [...lines, 'No A/B round yet: `pnpm bench ab default --control <experiment>`.'].join(
      '\n',
    )
  const current = rounds.filter((round) => round.source === latest.source)
  const scenarios = [...new Set(current.flatMap((round) => Object.keys(round.summary)))]
  const width = Math.max(...scenarios.map((scenario) => scenario.length)) + 2
  lines.push(
    '',
    `Verdicts from the ${current.length === 1 ? 'round' : `${current.length} rounds`} on the tree's latest sources (${latest.source.slice(0, 12)}), ` +
      'each with its readings, oldest first:',
    ...scenarios.map((scenario) => {
      const readings = current.flatMap((round) =>
        scenario in round.summary ? [`${round.kind} ${shown(round.summary[scenario])}`] : [],
      )
      return `  ${scenario.padEnd(width)}${verdict(current, scenario)}: ${readings.join(', ')}`
    }),
  )
  const missing = [
    ...(['default', 'small'] as const)
      .filter((kind) => !current.some((round) => round.kind === kind))
      .map((kind) => `a ${kind} round`),
    ...(hasSizes(experiment) ? [] : ['a size comparison']),
  ]
  if (missing.length > 0) lines.push('', `Missing: ${missing.join(', ')}.`)
  if (rounds.length > current.length)
    lines.push(`${rounds.length - current.length} older rounds measured other sources.`)
  if (sourceHash(ROOT) !== latest.source)
    lines.push("This checkout's sources differ from the latest round's.")
  return lines.join('\n')
}
