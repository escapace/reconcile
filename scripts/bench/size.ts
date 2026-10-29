// The consumer bundle sizes of a tree, which the round has just built, against the control's when
// there is one, and the bytes each source module adds to one bundle. `plan.json` records the
// sources measured, so that a report counts a comparison only for the sources it judges.
import { existsSync, readFileSync, writeFileSync } from 'node:fs'
import { SourceMap, type SourceMapPayload } from 'node:module'
import path from 'node:path'
import type { OutputOptions } from 'rolldown'
import { bundleExports, packageEntry, sizeRows, sizeTable } from '../bundles'
import { entry } from '../framework/entry'
import { writeJson } from '../framework/files'
import { bundle, virtualModule } from '../rolldown'
import { packageHash, sourceHash } from './provenance'

/** The configuration `pnpm bench size` passes. */
interface Config {
  /** The control's source tree. */
  readonly control: string | undefined
  readonly directory: string
  /** The exports whose bundle to break down by source module. */
  readonly modules: readonly string[] | undefined
  readonly tree: string
}

/** The internal member names that the tree's package build renames, if any. */
function mangledNames(tree: string): readonly string[] | undefined {
  const constants = JSON.parse(
    readFileSync(path.join(tree, 'scripts', 'constants.json'), 'utf8'),
  ) as {
    readonly builds?: { readonly neutral: { readonly mangle?: string[] } }
    readonly mangle?: string[]
  }
  // Trees from before the Rolldown build list them among their esbuild options.
  return constants.mangle ?? constants.builds?.neutral.mangle
}

/** Minification with the renaming of `mangle`, when the tree's build renames members. */
const minification = (mangle: readonly string[] | undefined): OutputOptions['minify'] =>
  mangle === undefined
    ? true
    : { mangleProps: { include: new RegExp(`^(?:${mangle.join('|')})$`) } }

/** Counts one character of a bundle for the module that the source map entry `found` names. */
function tally(characters: Map<string, number>, found: ReturnType<SourceMap['findEntry']>): void {
  if ('originalSource' in found)
    characters.set(found.originalSource, (characters.get(found.originalSource) ?? 0) + 1)
}

/** The characters of `code` that `map` places in each module. */
function charactersByModule(code: string, map: SourceMap): Map<string, number> {
  const characters = new Map<string, number>()
  for (const [line, text] of code.split('\n').entries())
    for (let column = 0; column < text.length; column += 1)
      tally(characters, map.findEntry(line, column))
  return characters
}

/** The bytes each source module adds to the minified bundle of `names` from the tree's sources,
 * built with the package's renaming of internal properties, as `scripts/build.ts` builds it.
 * Each character of the bundle counts for the module that its source map places it in. */
async function moduleBytes(tree: string, names: readonly string[]): Promise<Map<string, number>> {
  const file = path.join(tree, '__modules.ts')
  const chunk = await bundle(
    {
      cwd: tree,
      input: file,
      platform: 'browser',
      plugins: [virtualModule(file, `export {${names.join(',')}} from './src/index.ts'`)],
      transform: { target: 'es2022' },
    },
    {
      // Source map paths are relative to the tree, as the table names modules.
      dir: tree,
      minify: minification(mangledNames(tree)),
      sourcemap: true,
    },
  )
  const map = new SourceMap(chunk.map as unknown as SourceMapPayload)
  return new Map(
    [...charactersByModule(chunk.code, map)].toSorted((left, right) => right[1] - left[1]),
  )
}

/** The built package of a tree, which the round's build step wrote. */
function builtEntry(tree: string): string {
  const file = packageEntry(tree)
  if (!existsSync(file)) throw new Error(`${tree} has no built package after its build step.`)
  return file
}

async function sizes(config: Config): Promise<string> {
  const tree = await bundleExports(builtEntry(config.tree), path.join(config.directory, 'tree'))
  if (config.control === undefined)
    return sizeTable(sizeRows(tree.rows), ['Exports', 'Minified', 'Gzip'])
  const control = await bundleExports(
    builtEntry(config.control),
    path.join(config.directory, 'control'),
  )
  const before = new Map(sizeRows(control.rows).map((row) => [row.name, row.values]))
  return sizeTable(sizeRows(tree.rows), ['Exports', 'Minified', 'Gzip'], before)
}

async function modules(config: Config, names: readonly string[]): Promise<string> {
  const rows = [...(await moduleBytes(config.tree, names))].map(([name, bytes]) => ({
    name,
    values: [bytes],
  }))
  writeFileSync(
    path.join(config.directory, 'modules.json'),
    `${JSON.stringify(rows, undefined, 2)}\n`,
  )
  if (config.control === undefined) return sizeTable(rows, ['Module', 'Bytes'])
  let control: Map<string, number>
  try {
    control = await moduleBytes(config.control, names)
  } catch (error) {
    // A control from before one of the exports has no bundle of them; any other failure stands.
    const { errors = [] } = error as { errors?: ReadonlyArray<{ code?: string }> }
    if (!errors.some(({ code }) => code === 'MISSING_EXPORT')) throw error
    console.log(`The control does not export all of ${names.join('+')}.`)
    control = new Map()
  }
  const before = new Map([...control].map(([name, bytes]) => [name, [bytes]]))
  return sizeTable(rows, ['Module', 'Bytes'], before)
}

/** The packages a size comparison built and measured; a module breakdown bundles the sources
 * instead. */
function packagesOf({ control, modules, tree }: Config) {
  if (modules !== undefined) return null
  return { control: control === undefined ? null : packageHash(control), tree: packageHash(tree) }
}

async function main(config: Config): Promise<number> {
  writeJson(path.join(config.directory, 'plan.json'), {
    modules: config.modules ?? null,
    packageSha256: packagesOf(config),
    sourceSha256: {
      control: config.control === undefined ? null : sourceHash(config.control),
      tree: sourceHash(config.tree),
    },
  })
  console.log(
    config.modules === undefined ? await sizes(config) : await modules(config, config.modules),
  )
  return 0
}

await entry(import.meta.filename, main)
