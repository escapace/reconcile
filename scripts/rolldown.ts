import assert from 'node:assert/strict'
import { readFileSync } from 'node:fs'
import path from 'node:path'
import {
  rolldown,
  type InputOptions,
  type OutputChunk,
  type OutputOptions,
  type Plugin,
} from 'rolldown'

const ROOT = path.resolve(import.meta.dirname, '..')

/** Serves `code` as the TypeScript module `file`, which need not exist; its relative imports
 * resolve from the directory of `file`. */
export const virtualModule = (file: string, code: string): Plugin => ({
  name: 'virtual-module',
  load: (id) => (id === file ? { code, moduleType: 'ts' } : undefined),
  resolveId: (id) => (id === file ? file : undefined),
})

/** Bundles `input` into one ES module chunk in memory. */
export async function bundle(
  input: InputOptions,
  output: OutputOptions = {},
): Promise<OutputChunk> {
  const build = await rolldown({ logLevel: 'warn', ...input })
  try {
    const { output: chunks } = await build.generate({
      codeSplitting: false,
      format: 'esm',
      ...output,
    })
    return chunks[0]
  } finally {
    await build.close()
  }
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
  const entryFile = path.join(ROOT, '__entry.ts')
  const hooking: Plugin = {
    load: {
      filter: { id: file },
      handler(loaded) {
        let code = readFileSync(loaded, 'utf8')
        for (const [anchor, hook] of hooks) {
          assert.equal(code.split(anchor).length, 2, `hook anchor moved: ${anchor}`)
          code = code.replace(anchor, anchor + hook)
        }
        hooked += 1
        return { code, moduleType: 'ts' }
      },
    },
    name: 'hooks',
  }
  const chunk = await bundle({
    cwd: ROOT,
    input: entryFile,
    platform: 'node',
    plugins: [virtualModule(entryFile, entry), hooking],
  })
  assert.equal(hooked, 1, `one source matches ${String(file)}`)
  // Imported from memory, the bundle leaves no file behind, however its process ends.
  const source = Buffer.from(chunk.code).toString('base64')
  return (await import(`data:text/javascript;base64,${source}`)) as unknown
}
