import { execFileSync } from 'node:child_process'
import { chmodSync, mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import path from 'node:path'
import { describe, expect, it } from 'vitest'
import { changedFiles, inputs, matches } from './fingerprint'

/** A git repository with a tracked file in each of two directories, an ignored file and an
 * untracked one. */
function repository(): string {
  const root = mkdtempSync(path.join(tmpdir(), 'reconcile-fingerprint-spec-'))
  const write = (file: string, text: string): void => {
    mkdirSync(path.dirname(path.join(root, file)), { recursive: true })
    writeFileSync(path.join(root, file), text)
  }
  write('src/a.ts', 'a')
  write('docs/guide.md', 'guide')
  write('.gitignore', 'ignored.txt\n')
  const git = (...arguments_: string[]): void => {
    execFileSync('git', arguments_, { cwd: root, stdio: 'ignore' })
  }
  git('init', '-q')
  git('add', '.')
  git('-c', 'user.name=spec', '-c', 'user.email=spec@example.com', 'commit', '-qm', 'initial')
  write('ignored.txt', 'ignored')
  write('src/new.ts', 'new')
  return root
}

describe('matches', () => {
  it('reads a trailing slash as a directory, `*.` as an extension and anything else as a path', () => {
    expect(matches('docs/guide.md', 'docs/')).toBe(true)
    expect(matches('docsx/guide.md', 'docs/')).toBe(false)
    expect(matches('lean/Spec.lean', '*.lean')).toBe(true)
    expect(matches('README.md', 'README.md')).toBe(true)
    expect(matches('src/README.md', 'README.md')).toBe(false)
  })
})

describe('inputs', () => {
  it('counts tracked and untracked files but not ignored or excluded ones', () => {
    const root = repository()
    const all = inputs([], root)
    expect(Object.keys(all.files)).toEqual([
      '.gitignore',
      'docs/guide.md',
      'src/a.ts',
      'src/new.ts',
    ])
    expect(Object.keys(inputs(['docs/'], root).files)).not.toContain('docs/guide.md')
  })

  it('changes with content, deletion and the executable bit, and not with excluded files', () => {
    const root = repository()
    const before = inputs(['docs/'], root)
    writeFileSync(path.join(root, 'docs/guide.md'), 'edited')
    expect(inputs(['docs/'], root).hash).toBe(before.hash)
    writeFileSync(path.join(root, 'src/a.ts'), 'b')
    const edited = inputs(['docs/'], root)
    expect(changedFiles(before.files, edited.files)).toEqual(['src/a.ts'])
    chmodSync(path.join(root, 'src/a.ts'), 0o755)
    const executable = inputs(['docs/'], root)
    expect(executable.hash).not.toBe(edited.hash)
    rmSync(path.join(root, 'src/a.ts'))
    expect(inputs(['docs/'], root).files['src/a.ts']).toBe('deleted')
  })
})
