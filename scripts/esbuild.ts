import assert from 'node:assert/strict'
import { mkdtempSync, readFileSync, realpathSync, rmSync, writeFileSync } from 'node:fs'
import { createRequire } from 'node:module'
import { tmpdir } from 'node:os'
import path from 'node:path'
import { pathToFileURL } from 'node:url'

const ROOT = path.resolve(import.meta.dirname, '..')

/** The part of the esbuild API the tooling uses. */
export interface Esbuild {
  readonly version: string
  build: (options: Record<string, unknown>) => Promise<{
    outputFiles: Array<{ contents: Uint8Array }>
  }>
}

/** Loads the esbuild that the build tool esroll resolves, so every tool uses the same version. */
export function loadEsbuild(): Esbuild {
  const esroll = realpathSync(path.join(ROOT, 'node_modules', 'esroll'))
  return createRequire(path.join(esroll, 'package.json'))('esbuild') as Esbuild
}

/** A statement of a hooked source and the code inserted after it. */
export type Hook = readonly [anchor: string, hook: string]

/**
 * Bundles `entry`, module source resolved from the repository root, with each hook's code
 * inserted after its anchor in the one source `file` matches, and imports the bundle.
 *
 * @remarks
 * Every module the entry reaches is bundled once, so the hooked source and the modules beside it
 * share their imports. Each anchor must occur once.
 */
export async function bundleWithHooks(
  entry: string,
  file: RegExp,
  hooks: readonly Hook[],
): Promise<unknown> {
  let hooked = 0
  const result = await loadEsbuild().build({
    bundle: true,
    format: 'esm',
    platform: 'node',
    plugins: [
      {
        name: 'hooks',
        setup(build: {
          onLoad: (
            options: { filter: RegExp },
            callback: (arguments_: { path: string }) => unknown,
          ) => void
        }) {
          build.onLoad({ filter: file }, ({ path: loaded }) => {
            let contents = readFileSync(loaded, 'utf8')
            for (const [anchor, hook] of hooks) {
              assert.equal(contents.split(anchor).length, 2, `hook anchor moved: ${anchor}`)
              contents = contents.replace(anchor, anchor + hook)
            }
            hooked += 1
            return { contents, loader: 'ts' }
          })
        },
      },
    ],
    stdin: { contents: entry, loader: 'ts', resolveDir: ROOT },
    target: 'esnext',
    write: false,
  })
  assert.equal(hooked, 1, `one source matches ${String(file)}`)
  const directory = mkdtempSync(path.join(tmpdir(), 'reconcile-hooks-'))
  try {
    const bundle = path.join(directory, 'index.mjs')
    writeFileSync(bundle, result.outputFiles[0].contents)
    return (await import(pathToFileURL(bundle).href)) as unknown
  } finally {
    rmSync(directory, { force: true, recursive: true })
  }
}
