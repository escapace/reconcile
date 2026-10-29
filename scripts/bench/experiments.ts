import { existsSync, mkdirSync, readdirSync, readFileSync } from 'node:fs'
import path from 'node:path'
import { Blocked, UsageError } from '../framework/command'
import { writeJson } from '../framework/files'
import { fromUser, STATE } from '../framework/paths'
import { stampedDirectory } from '../framework/round'
import { frozenHash, sourceHash } from './provenance'

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
  /** The control's frozen workloads and library sources as frozen; absent in experiments from
   * before they were pinned, whose control is taken as it is now. */
  readonly frozenWorkloadSha256?: string
  readonly sourceSha256?: string
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

/** Records a frozen control, with the hashes that pin it, which makes its directory an
 * experiment. */
export function completeExperiment(
  directory: string,
  record: Omit<ExperimentRecord, 'frozenWorkloadSha256' | 'sourceSha256'>,
): void {
  const tree = path.join(directory, 'tree')
  writeJson(path.join(directory, 'experiment.json'), {
    ...record,
    frozenWorkloadSha256: frozenHash(tree),
    sourceSha256: sourceHash(tree),
  })
}

/** The record of an experiment directory, or undefined when it has none or it cannot be read. */
function recordOf(directory: string): ExperimentRecord | undefined {
  try {
    return JSON.parse(
      readFileSync(path.join(directory, 'experiment.json'), 'utf8'),
    ) as ExperimentRecord
  } catch {
    return undefined
  }
}

/** The complete experiments, oldest first; one whose record cannot be read is skipped. */
function experiments(): Experiment[] {
  if (!existsSync(EXPERIMENTS)) return []
  return readdirSync(EXPERIMENTS)
    .flatMap((name) => {
      const directory = path.join(EXPERIMENTS, name)
      const record = recordOf(directory)
      return record === undefined
        ? []
        : [{ directory, name, record, tree: path.join(directory, 'tree') }]
    })
    .toSorted((left, right) => left.record.created.localeCompare(right.record.created))
}

/** The experiment `value` names: `latest`, a name, its directory or its control's `tree/`. */
function findExperiment(value: string): Experiment | undefined {
  const known = experiments()
  if (value === 'latest') return known.at(-1)
  const named = known.find((experiment) => experiment.name === value)
  if (named !== undefined) return named
  const resolved = fromUser(value)
  return known.find(
    (experiment) => experiment.directory === resolved || experiment.tree === resolved,
  )
}

const unknown = (value: string, what: string): UsageError => {
  const recent = experiments()
    .slice(-3)
    .map((experiment) => experiment.name)
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

/** The control's sources as the experiment pinned them, or as they are now when it predates
 * pinning. */
export const pinnedSource = (experiment: Experiment): string =>
  experiment.record.sourceSha256 ?? sourceHash(experiment.tree)

/** Refuses an experiment whose control changed after it was frozen: its rounds would then
 * compare against two controls. */
function assertPinned(experiment: Experiment): void {
  const { frozenWorkloadSha256, sourceSha256 } = experiment.record
  const changed = [
    sourceSha256 !== undefined && sourceSha256 !== sourceHash(experiment.tree) && 'src/',
    frozenWorkloadSha256 !== undefined &&
      frozenWorkloadSha256 !== frozenHash(experiment.tree) &&
      'perf/',
  ].filter((part) => part !== false)
  if (changed.length > 0)
    throw new Blocked(
      `the control of experiment ${experiment.name} changed after it was frozen (${changed.join(' and ')}); ` +
        'freeze a new control with `pnpm bench control`',
    )
}

/** The control `value` names: an experiment, as `resolveExperiment` finds it, whose control must
 * be as it was frozen, or a source tree. */
export function resolveControl(value: string): Control {
  const experiment = findExperiment(value)
  if (experiment !== undefined) {
    assertPinned(experiment)
    return { rounds: path.join(experiment.directory, 'rounds'), tree: experiment.tree }
  }
  const tree = fromUser(value)
  if (existsSync(path.join(tree, 'src', 'index.ts'))) return { rounds: undefined, tree }
  throw unknown(value, 'experiment or source tree')
}

/** The directories of an experiment's rounds, oldest first. */
export const roundsOf = (experiment: Experiment): string[] =>
  readdirSync(path.join(experiment.directory, 'rounds'))
    .toSorted()
    .map((name) => path.join(experiment.directory, 'rounds', name))
