import { spawnSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { readFileSync, statSync } from 'node:fs'
import path from 'node:path'
import { ROOT } from './paths'

/**
 * What a round's result depends on: the content of every file of the working tree that the round
 * does not exclude, tracked or untracked but not ignored, and the environment it runs in. Two
 * rounds with the same hash ran on the same inputs.
 */
export interface Inputs {
  readonly environment: Readonly<Record<string, string>>
  readonly files: Readonly<Record<string, string>>
  readonly hash: string
}

/** Whether `file` matches a pattern: `dir/` names a directory, `*.ext` an extension, and any
 * other pattern one path. */
export function matches(file: string, pattern: string): boolean {
  if (pattern.endsWith('/')) return file.startsWith(pattern)
  if (pattern.startsWith('*.')) return file.endsWith(pattern.slice(1))
  return file === pattern
}

/** The working tree's files as git lists them: tracked, and untracked but not ignored. */
export function treeFiles(root = ROOT): string[] {
  const listed = spawnSync(
    'git',
    ['ls-files', '-z', '--cached', '--others', '--exclude-standard'],
    {
      cwd: root,
      encoding: 'utf8',
    },
  )
  if (listed.status !== 0) throw new Error(`git ls-files failed in ${root}: ${listed.stderr}`)
  return [...new Set(listed.stdout.split('\0').filter((file) => file !== ''))].sort()
}

const digest = (data: string | Buffer): string => createHash('sha256').update(data).digest('hex')

/** A file's content hash, marked when the file is executable; a tracked file that was deleted
 * counts as such. */
function contentOf(file: string): string {
  let mode: number
  try {
    ;({ mode } = statSync(file))
  } catch {
    return 'deleted'
  }
  return `${digest(readFileSync(file)).slice(0, 16)}${(mode & 0o111) === 0 ? '' : '+x'}`
}

/** What a round depends on besides the files: the Node runtime and the options it runs with,
 * the platform, and the installed dependencies. */
function environmentOf(root: string): Record<string, string> {
  let modules = 'missing'
  try {
    modules = digest(readFileSync(path.join(root, 'node_modules', '.pnpm', 'lock.yaml'))).slice(
      0,
      16,
    )
  } catch {
    // Not installed: rounds then fail, and record nothing.
  }
  return {
    modules,
    node: process.version,
    nodeOptions: process.env.NODE_OPTIONS ?? '',
    platform: `${process.platform}-${process.arch}`,
  }
}

/** The inputs of a round that ignores the files `exclude` matches. */
export function inputs(exclude: readonly string[], root = ROOT): Inputs {
  const files: Record<string, string> = {}
  for (const file of treeFiles(root))
    if (!exclude.some((pattern) => matches(file, pattern)))
      files[file] = contentOf(path.join(root, file))
  const environment = environmentOf(root)
  return { environment, files, hash: digest(JSON.stringify([files, environment])) }
}

/** The files whose content differs between two sets of inputs, added and removed ones included. */
export function changedFiles(before: Inputs['files'], after: Inputs['files']): string[] {
  const names = new Set([...Object.keys(before), ...Object.keys(after)])
  return [...names].filter((name) => before[name] !== after[name]).sort()
}

/** The environment entries that differ between two sets of inputs. */
export function changedEnvironment(
  before: Inputs['environment'],
  after: Inputs['environment'],
): string[] {
  return Object.keys(after).filter((key) => before[key] !== after[key])
}
