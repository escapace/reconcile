import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import path from 'node:path'
import { afterEach, describe, expect, it } from 'vitest'
import { auditSource, configuredModules } from './axioms'

const directories: string[] = []

/** A checkout holding `files`, by path. */
function checkout(files: Readonly<Record<string, string>>): string {
  const root = mkdtempSync(path.join(tmpdir(), 'reconcile-axioms-spec-'))
  directories.push(root)
  for (const [file, text] of Object.entries(files)) {
    mkdirSync(path.dirname(path.join(root, file)), { recursive: true })
    writeFileSync(path.join(root, file), text)
  }
  return root
}

/** A Lake configuration with one library of `roots`. */
const lakefile = (roots: string): string => `[[lean_lib]]\nroots = [${roots}]\n`

afterEach(() => {
  for (const directory of directories.splice(0)) rmSync(directory, { force: true, recursive: true })
})

describe('the audited modules', () => {
  // The `test` round does not read the Lean sources, so these checkouts are the spec's own; the
  // `lean` round's audit checks the real one.
  it('are the roots of the Lake library, which list every Lean file once', () => {
    const config = '[package]\nname = "x"\n\n[[lean_lib]]\nroots = [\n  "A",\n  "Graph.B",\n]\n'
    expect(
      configuredModules(
        checkout({ 'lakefile.toml': config, 'lean/A.lean': '', 'lean/Graph/B.lean': '' }),
      ),
    ).toEqual(['A', 'Graph.B'])
  })

  it('refuse a Lean file the library does not list, a root without a file and a duplicate', () => {
    const unlisted = checkout({
      'lakefile.toml': lakefile('"A"'),
      'lean/A.lean': '',
      'lean/B.lean': '',
    })
    expect(() => configuredModules(unlisted)).toThrow('coverage mismatch: B')
    const missing = checkout({ 'lakefile.toml': lakefile('"A", "C"'), 'lean/A.lean': '' })
    expect(() => configuredModules(missing)).toThrow('coverage mismatch: C')
    const duplicate = checkout({ 'lakefile.toml': lakefile('"A", "A"'), 'lean/A.lean': '' })
    expect(() => configuredModules(duplicate)).toThrow('duplicate')
  })
})

describe('the audit program', () => {
  it('imports the modules and allows the standard axioms only', () => {
    const source = auditSource(['A', 'Graph.B'])
    expect(source).toMatch(/^import A\nimport Graph\.B\nimport Lean\n/)
    expect(source).toContain('#[`A, `Graph.B]')
    expect(source).toContain('#[`propext, `Classical.choice, `Quot.sound]')
    expect(source).not.toContain('_private.')
  })

  it('for the control, allows no axiom and requires a private declaration first', () => {
    const source = auditSource(['A'], [], true)
    expect(source).toContain('let allowed : Array Lean.Name := #[]')
    expect(source.indexOf('_private.')).toBeLessThan(source.indexOf('CollectAxioms'))
  })
})
