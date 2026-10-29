// Freezes a control: exports a revision, or the working tree with its uncommitted changes, into
// an experiment's `tree/`, and records what it holds.
import { spawnSync } from 'node:child_process'
import { mkdirSync, symlinkSync, writeFileSync } from 'node:fs'
import path from 'node:path'
import { entry } from '../framework/entry'
import { ROOT } from '../framework/paths'
import { copyTree } from '../framework/tree'
import type { ExperimentRecord } from './experiments'

/** The configuration `pnpm bench control` passes. */
interface Config {
  /** Links this checkout's dependencies into the tree, so that it can be built. */
  readonly build: boolean
  readonly directory: string
  readonly revision: string
  readonly worktree: boolean
}

function git(...arguments_: string[]): string {
  const result = spawnSync('git', arguments_, { cwd: ROOT, encoding: 'buffer', maxBuffer: 1 << 30 })
  if (result.status !== 0)
    throw new Error(`git ${arguments_.join(' ')} failed: ${result.stderr.toString()}`)
  return result.stdout.toString()
}

/** Exports `revision` into `tree` as `git archive` writes it. */
function archive(revision: string, tree: string): void {
  const tar = spawnSync('git', ['archive', '--format=tar', revision], {
    cwd: ROOT,
    maxBuffer: 1 << 30,
  })
  if (tar.status !== 0) throw new Error(`git archive ${revision} failed: ${tar.stderr.toString()}`)
  const extract = spawnSync('tar', ['-x', '-C', tree], { input: tar.stdout })
  if (extract.status !== 0) throw new Error(`tar failed: ${extract.stderr.toString()}`)
}

async function main(config: Config): Promise<number> {
  const tree = path.join(config.directory, 'tree')
  mkdirSync(tree, { recursive: true })
  if (config.worktree) copyTree(tree)
  else archive(config.revision, tree)
  // The control uses this checkout's dependencies, as the measured tree does.
  if (config.build) symlinkSync(path.join(ROOT, 'node_modules'), path.join(tree, 'node_modules'))
  const record: ExperimentRecord = {
    commit: git('rev-parse', `${config.worktree ? 'HEAD' : config.revision}^{commit}`).trim(),
    created: new Date().toISOString(),
    worktree: config.worktree,
  }
  writeFileSync(
    path.join(config.directory, 'experiment.json'),
    `${JSON.stringify(record, undefined, 2)}\n`,
  )
  return await Promise.resolve(0)
}

await entry(import.meta.filename, main)
