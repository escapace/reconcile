import { existsSync, mkdirSync, readdirSync, readFileSync } from 'node:fs'
import path from 'node:path'
import { UsageError } from '../framework/command'
import { STATE } from '../framework/paths'

/** Where experiments are kept: each holds a frozen control tree and the rounds measured
 * against it. */
export const EXPERIMENTS = path.join(STATE, 'experiments')

/** What `experiment.json` records of the control. */
export interface ExperimentRecord {
  /** The commit the control was exported from. */
  readonly commit: string
  readonly created: string
  /** Whether the control holds the working tree's uncommitted changes. */
  readonly worktree: boolean
}

export interface Experiment {
  readonly directory: string
  readonly name: string
  readonly record: ExperimentRecord
  /** The control's source tree. */
  readonly tree: string
}

/** A new experiment directory, named after its time and label. */
export function createExperiment(label: string): string {
  const stamp = new Date().toISOString().slice(0, 19).replaceAll(/[-:]/g, '').replace('T', '-')
  const directory = path.join(EXPERIMENTS, `${stamp}-${label}`)
  mkdirSync(path.join(directory, 'rounds'), { recursive: true })
  return directory
}

const names = (): string[] =>
  existsSync(EXPERIMENTS)
    ? readdirSync(EXPERIMENTS)
        .filter((name) => existsSync(path.join(EXPERIMENTS, name, 'experiment.json')))
        .toSorted()
    : []

/** The experiment `value` names: its directory, its name, or `latest` for the newest. */
export function resolveExperiment(value: string): Experiment {
  const known = names()
  const named = value === 'latest' ? known.at(-1) : value
  const directory =
    named !== undefined && known.includes(named)
      ? path.join(EXPERIMENTS, named)
      : path.resolve(value)
  const file = path.join(directory, 'experiment.json')
  if (!existsSync(file))
    throw new UsageError(
      `no experiment "${value}"; start one with \`pnpm bench control\`` +
        (known.length === 0 ? '' : `, or name one of ${known.slice(-3).join(', ')}`),
    )
  return {
    directory,
    name: path.basename(directory),
    record: JSON.parse(readFileSync(file, 'utf8')) as ExperimentRecord,
    tree: path.join(directory, 'tree'),
  }
}

/** The directories of an experiment's rounds, oldest first. */
export const roundsOf = (experiment: Experiment): string[] =>
  readdirSync(path.join(experiment.directory, 'rounds'))
    .toSorted()
    .map((name) => path.join(experiment.directory, 'rounds', name))
