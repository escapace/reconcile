import { execFileSync } from 'node:child_process'
import { mkdtempSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import path from 'node:path'
import { expect, it } from 'vitest'
import { loadEsbuild } from '../../scripts/esbuild'

/** Bundles a driver without helpers, which would themselves read the standard prototypes,
 * imports it in a child process with the given flags and returns its `result`. */
async function runDriver(
  fixture: string,
  flags: readonly string[],
): Promise<{ cases: number; failures: string[] }> {
  const directory = mkdtempSync(path.join(tmpdir(), 'reconcile-prototypes-'))
  try {
    const result = await loadEsbuild().build({
      bundle: true,
      entryPoints: [path.join(import.meta.dirname, 'fixtures', fixture)],
      format: 'esm',
      logLevel: 'warning',
      platform: 'neutral',
      write: false,
    })
    const driver = path.join(directory, 'driver.mjs')
    writeFileSync(driver, result.outputFiles[0].contents)
    const print =
      'const { result } = await import(process.argv[1]); console.log(JSON.stringify(result))'
    return JSON.parse(
      execFileSync(process.execPath, [...flags, '--input-type=module', '-e', print, driver], {
        encoding: 'utf8',
        stdio: ['ignore', 'pipe', 'ignore'],
        timeout: 60_000,
      }),
    ) as { cases: number; failures: string[] }
  } finally {
    rmSync(directory, { force: true, recursive: true })
  }
}

// Properties added to Object.prototype or Array.prototype change no internal read, write,
// descriptor or iterator close, and objects the library builds hold their own data whatever
// Object.prototype holds.
it('keeps every operation independent of added standard-prototype properties', async () => {
  const output = await runDriver('standard-prototypes.ts', [])
  expect(output.cases).toBeGreaterThan(100)
  expect(output.failures).toEqual([])
}, 90_000)

// Under frozen intrinsics a recipe's assignment behaves as plain assignment, and every new object
// holds the keys standard prototypes hold as accessors.
it('behaves as plain assignment under node --frozen-intrinsics', async () => {
  const output = await runDriver('frozen-intrinsics.ts', ['--frozen-intrinsics'])
  expect(output.cases).toBe(7)
  expect(output.failures).toEqual([])
}, 90_000)
