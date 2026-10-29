import { existsSync, mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs'
import path from 'node:path'
import { UsageError } from '../framework/command'
import { STATE } from '../framework/paths'
import { stampedDirectory } from '../framework/round'

/** Where experiments are kept: each holds a frozen control tree and the rounds measured
 * against it. */
export const EXPERIMENTS = path.join(STATE, 'experiments')

/** What `experiment.json` records of the control, once it is complete. */
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

/** The control a command compares with: an experiment's, whose rounds it keeps, or any source
 * tree, whose rounds go with the others. */
export interface Control {
  readonly rounds: string | undefined
  readonly tree: string
}

/** A new experiment directory, named after its time and label; it counts as an experiment once
 * `completeExperiment` records it. */
export function createExperiment(label: string): string {
  const directory = stampedDirectory(label, EXPERIMENTS)
  mkdirSync(path.join(directory, 'rounds'))
  return directory
}

/** Records a frozen control, which makes its directory an experiment. */
export function completeExperiment(directory: string, record: ExperimentRecord): void {
  writeFileSync(
    path.join(directory, 'experiment.json'),
    `${JSON.stringify(record, undefined, 2)}\n`,
  )
}

const recordOf = (directory: string): ExperimentRecord =>
  JSON.parse(readFileSync(path.join(directory, 'experiment.json'), 'utf8')) as ExperimentRecord

/** The names of the complete experiments, oldest first. */
const names = (): string[] =>
  existsSync(EXPERIMENTS)
    ? readdirSync(EXPERIMENTS)
        .filter((name) => existsSync(path.join(EXPERIMENTS, name, 'experiment.json')))
        .map((name) => ({ created: recordOf(path.join(EXPERIMENTS, name)).created, name }))
        .toSorted((left, right) => left.created.localeCompare(right.created))
        .map(({ name }) => name)
    : []

/** The experiment `value` names, by its directory, its name or `latest`, if there is one. */
function findExperiment(value: string): Experiment | undefined {
  const known = names()
  const named = value === 'latest' ? known.at(-1) : value
  const directory =
    named !== undefined && known.includes(named)
      ? path.join(EXPERIMENTS, named)
      : path.resolve(value)
  if (!existsSync(path.join(directory, 'experiment.json'))) return undefined
  return {
    directory,
    name: path.basename(directory),
    record: recordOf(directory),
    tree: path.join(directory, 'tree'),
  }
}

const unknown = (value: string, what: string): UsageError => {
  const recent = names().slice(-3)
  return new UsageError(
    `no ${what} "${value}"; start an experiment with \`pnpm bench control\`` +
      (recent.length === 0 ? '' : `, or name one of ${recent.join(', ')}`),
  )
}

/** The experiment `value` names: its directory, its name, or `latest` for the newest. */
export function resolveExperiment(value: string): Experiment {
  const experiment = findExperiment(value)
  if (experiment === undefined) throw unknown(value, 'experiment')
  return experiment
}

/** The control `value` names: an experiment, as `resolveExperiment` finds it, or a source tree. */
export function resolveControl(value: string): Control {
  const experiment = findExperiment(value)
  if (experiment !== undefined)
    return { rounds: path.join(experiment.directory, 'rounds'), tree: experiment.tree }
  const tree = path.resolve(value)
  if (existsSync(path.join(tree, 'src', 'index.ts'))) return { rounds: undefined, tree }
  throw unknown(value, 'experiment or source tree')
}

/** The directories of an experiment's rounds, oldest first. */
export const roundsOf = (experiment: Experiment): string[] =>
  readdirSync(path.join(experiment.directory, 'rounds'))
    .toSorted()
    .map((name) => path.join(experiment.directory, 'rounds', name))
