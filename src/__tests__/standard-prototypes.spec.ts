import { execFileSync } from 'node:child_process'
import { mkdtempSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import path from 'node:path'
import { pathToFileURL } from 'node:url'
import { expect, it } from 'vitest'
import { loadEsbuild } from '../../scripts/esbuild'

/** When a child process calls SES `lockdown`, before or after it imports the driver, and with
 * which `overrideTaming`. */
interface Lockdown {
  readonly order: 'after' | 'before'
  readonly taming: 'default' | 'severe'
}

/** A driver's result, and whether the runtime froze `Array.prototype` by the time it ran. */
interface DriverResult {
  readonly cases: number
  readonly failures: string[]
  readonly frozen: boolean
  readonly outcomes?: string[]
}

const SES = import.meta.resolve('ses')

// Imports the driver, locking down before or after when asked, and prints its `result`, or what
// its `run` returns, on a line of its own after a record separator.
const PRINT = `const [driver, ses, order, taming] = process.argv.slice(1)
const lock = async () => {
  await import(ses)
  lockdown(taming === 'default' ? undefined : { overrideTaming: taming })
}
if (order === 'after') await lock()
const module = await import(driver)
if (order === 'before') await lock()
const result = module.run?.() ?? module.result
console.log('\\u001e' + JSON.stringify({ ...result, frozen: Object.isFrozen(Array.prototype) }))`

/** Bundles a driver without helpers, which would themselves read the standard prototypes,
 * imports it in a child process with the given flags, after or before SES `lockdown` when given,
 * and returns its result. */
async function runDriver(
  fixture: string,
  flags: readonly string[],
  lockdown?: Lockdown,
): Promise<DriverResult> {
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
    const output = execFileSync(
      process.execPath,
      [
        ...flags,
        '--input-type=module',
        '-e',
        PRINT,
        pathToFileURL(driver).href,
        SES,
        lockdown?.order ?? 'none',
        lockdown?.taming ?? 'default',
      ],
      { encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'], timeout: 60_000 },
    )
    return JSON.parse(output.slice(output.lastIndexOf('\u001e') + 1)) as DriverResult
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

// Every function on every value kind behaves the same when standard methods are accessors, as
// `node --frozen-intrinsics` makes them, as in an ordinary runtime.
it('behaves the same for every value kind under node --frozen-intrinsics', async () => {
  const plain = await runDriver('hardened-kinds.ts', [])
  const frozen = await runDriver('hardened-kinds.ts', ['--frozen-intrinsics'])
  expect(plain.failures).toEqual([])
  expect(plain.cases).toBeGreaterThan(120)
  expect(plain.frozen).toBe(false)
  expect(frozen.frozen).toBe(true)
  expect(frozen.outcomes).toEqual(plain.outcomes)
}, 90_000)

// SES `lockdown` freezes every intrinsic and, with severe override taming, turns the methods of
// standard prototypes into accessors. Every function on every value kind behaves as in an ordinary
// runtime, whether the library is imported before or after `lockdown`.
it('behaves the same for every value kind under SES, imported before or after lockdown', async () => {
  const plain = await runDriver('hardened-kinds.ts', [])
  for (const order of ['before', 'after'] as const)
    for (const taming of ['default', 'severe'] as const) {
      const locked = await runDriver('hardened-kinds.ts', [], { order, taming })
      expect(locked.frozen).toBe(true)
      expect(locked.outcomes, `${order} lockdown, ${taming} taming`).toEqual(plain.outcomes)
    }
}, 120_000)
