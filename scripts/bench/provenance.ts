// What a measurement measured: hashes of a tree's library sources, built package and frozen
// workloads, of the workloads every tree shares, and the tree's commit. Rounds whose hashes differ measured
// different things, so they are never judged together.
import { spawnSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { existsSync, readdirSync, readFileSync, realpathSync } from 'node:fs'
import path from 'node:path'
import { packageEntry } from '../bundles'
import { Blocked } from '../framework/command'
import { ROOT } from '../framework/paths'

const sha256 = (data: string | Buffer): string => createHash('sha256').update(data).digest('hex')

/** A hash of the named files of `root`, a missing file included as such. */
const filesHash = (root: string, files: readonly string[]): string =>
  sha256(
    files
      .map((file) => {
        const full = path.join(root, file)
        return `${file}\0${existsSync(full) ? sha256(readFileSync(full)) : 'missing'}`
      })
      .join('\n'),
  )

/** A hash of the tree's library sources: every file under `src/` but its specs and hidden
 * files, which tells two rounds on the same code apart from rounds on changed code. */
export function sourceHash(tree: string): string {
  const files = readdirSync(path.join(tree, 'src'), { recursive: true, withFileTypes: true })
    .filter((file) => file.isFile())
    .map((file) => path.relative(tree, path.join(file.parentPath, file.name)))
    .filter(
      (file) => !file.split(path.sep).some((part) => part === '__tests__' || part.startsWith('.')),
    )
    .toSorted()
  return filesHash(tree, files)
}

/** A hash of the tree's built package, which its build step wrote. */
export function packageHash(tree: string): string {
  const file = packageEntry(tree)
  if (!existsSync(file)) throw new Error(`${tree} has no built package after its build step.`)
  return sha256(readFileSync(file))
}

/** The frozen workloads, which the control and the measured tree must share. */
const FROZEN = ['perf/scenarios.ts', 'perf/config.ts', 'perf/profile-harness.ts']

/** A hash of the tree's frozen workloads. */
export const frozenHash = (tree: string): string => filesHash(tree, FROZEN)

/** A hash of the workloads every tree runs from this checkout: the serialization and small
 * workloads and the diagnostics. */
export const sharedHash = (): string =>
  filesHash(ROOT, ['scripts/bench-workloads.ts', 'scripts/bench/diagnostics.ts'])

/** Refuses to compare two trees whose frozen workloads differ: their scenarios are not the same
 * work, so neither their times nor their counts compare. */
export function assertSameWorkloads(control: string, tree: string): void {
  if (frozenHash(control) !== frozenHash(tree))
    throw new Blocked(
      `the frozen workloads in perf/ of ${control} and ${tree} differ, so their scenarios are ` +
        'not the same work; compare trees that share them',
    )
}

/** The commit of the tree and whether it has uncommitted changes, or null unless the tree is
 * itself the top of a git checkout. */
export function gitState(tree: string): { commit: string; dirty: boolean } | null {
  const git = (...arguments_: string[]): string | undefined => {
    const result = spawnSync('git', ['-C', tree, ...arguments_], { encoding: 'utf8' })
    return result.status === 0 ? result.stdout.trim() : undefined
  }
  const top = git('rev-parse', '--show-toplevel')
  if (top === undefined || realpathSync(top) !== realpathSync(tree)) return null
  return {
    commit: git('rev-parse', 'HEAD') ?? '',
    dirty: (git('status', '--porcelain') ?? '') !== '',
  }
}
