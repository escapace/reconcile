import { realpathSync } from 'node:fs'
import { createRequire } from 'node:module'
import path from 'node:path'

const ROOT = path.resolve(import.meta.dirname, '..')

/** The part of the esbuild API the tooling uses. */
export interface Esbuild {
  readonly version: string
  build: (options: Record<string, unknown>) => Promise<{
    metafile: { inputs: Record<string, unknown> }
    outputFiles: Array<{ contents: Uint8Array }>
  }>
  buildSync: (options: Record<string, unknown>) => unknown
}

/** Loads the esbuild that the build tool esroll resolves, so every tool uses the same version. */
export function loadEsbuild(): Esbuild {
  const esroll = realpathSync(path.join(ROOT, 'node_modules', 'esroll'))
  return createRequire(path.join(esroll, 'package.json'))('esbuild') as Esbuild
}
