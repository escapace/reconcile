// Freezes a control: exports a commit, or the working tree with its uncommitted changes, into an
// experiment's `tree/`, and links this checkout's dependencies into it, so that both trees build
// and resolve their imports with the same ones.
import { spawnSync } from 'node:child_process'
import { mkdirSync, symlinkSync } from 'node:fs'
import path from 'node:path'
import { entry } from '../framework/entry'
import { ROOT } from '../framework/paths'
import { copyTree } from '../framework/tree'

/** The configuration `pnpm bench control` passes. */
interface Config {
  readonly commit: string
  readonly directory: string
  readonly worktree: boolean
}

/** Exports `commit` into `tree` as `git archive` writes it. */
function archive(commit: string, tree: string): void {
  const tar = spawnSync('git', ['archive', '--format=tar', commit], {
    cwd: ROOT,
    maxBuffer: 1 << 30,
  })
  if (tar.status !== 0) throw new Error(`git archive ${commit} failed: ${tar.stderr.toString()}`)
  const extract = spawnSync('tar', ['-x', '-C', tree], { input: tar.stdout })
  if (extract.status !== 0) throw new Error(`tar failed: ${extract.stderr.toString()}`)
}

async function main(config: Config): Promise<number> {
  const tree = path.join(config.directory, 'tree')
  mkdirSync(tree, { recursive: true })
  if (config.worktree) copyTree(tree)
  else archive(config.commit, tree)
  symlinkSync(path.join(ROOT, 'node_modules'), path.join(tree, 'node_modules'))
  return await Promise.resolve(0)
}

await entry(import.meta.filename, main)
