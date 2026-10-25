import { execFileSync } from 'node:child_process'
import { mkdtempSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import path from 'node:path'
import { pathToFileURL } from 'node:url'
import { loadEsbuild } from '../../../scripts/esbuild'

/** When a child process calls SES `lockdown`, before or after it imports the driver, and with
 * which `overrideTaming`. */
export interface Lockdown {
  readonly order: 'after' | 'before'
  readonly taming: 'default' | 'severe'
}

/** A driver's result, and whether the runtime froze `Array.prototype` by the time it ran. */
export interface DriverResult {
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

/** Bundles a driver from this directory without helpers, which would themselves read the
 * standard prototypes, imports it in a child process with the given flags, after or before SES
 * `lockdown` when given, and returns its result. */
export async function runDriver(
  fixture: string,
  flags: readonly string[],
  lockdown?: Lockdown,
): Promise<DriverResult> {
  const directory = mkdtempSync(path.join(tmpdir(), 'reconcile-prototypes-'))
  try {
    const result = await loadEsbuild().build({
      bundle: true,
      entryPoints: [path.join(import.meta.dirname, fixture)],
      // The invariants driver's generator reads Node's assert; the child process is Node.
      external: ['node:*'],
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
      { encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'], timeout: 120_000 },
    )
    return JSON.parse(output.slice(output.lastIndexOf('\u001e') + 1)) as DriverResult
  } finally {
    rmSync(directory, { force: true, recursive: true })
  }
}
