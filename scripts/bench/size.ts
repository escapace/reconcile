// The consumer bundle sizes of a tree, which the round has just built, against the control's when
// there is one, and the bytes each source module adds to one bundle. `plan.json` records the
// sources measured, so that a report counts a comparison only for the sources it judges.
import { existsSync, readFileSync, writeFileSync } from 'node:fs'
import path from 'node:path'
import { bundleExports, packageEntry, sizeRows, sizeTable } from '../bundles'
import { loadEsbuild } from '../esbuild'
import { entry } from '../framework/entry'
import { writeJson } from '../framework/files'
import { sourceHash } from './provenance'

/** The configuration `pnpm bench size` passes. */
interface Config {
  /** The control's source tree. */
  readonly control: string | undefined
  readonly directory: string
  /** The exports whose bundle to break down by source module. */
  readonly modules: readonly string[] | undefined
  readonly tree: string
}

/** The bytes each source module adds to the bundle of `names` from the tree's sources, built
 * with the package's renaming of internal properties, as `scripts/build.ts` builds it. */
async function moduleBytes(tree: string, names: readonly string[]): Promise<Map<string, number>> {
  const { builds } = JSON.parse(
    readFileSync(path.join(tree, 'scripts', 'constants.json'), 'utf8'),
  ) as {
    builds: { neutral: { mangle?: string[] } }
  }
  const { mangle } = builds.neutral
  const result = await loadEsbuild().build({
    absWorkingDir: tree,
    bundle: true,
    format: 'esm',
    metafile: true,
    minify: true,
    platform: 'browser',
    stdin: { contents: `export {${names.join(',')}} from './src/index.ts'`, resolveDir: tree },
    target: 'es2022',
    write: false,
    ...(mangle === undefined ? {} : { mangleProps: new RegExp(`^(?:${mangle.join('|')})$`) }),
  })
  const [output] = Object.values(result.metafile!.outputs)
  return new Map(
    Object.entries(output.inputs)
      .map(([file, { bytesInOutput }]) => [file, bytesInOutput] as const)
      .filter(([, bytes]) => bytes > 0)
      .toSorted((left, right) => right[1] - left[1]),
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
    if (!(error as Error).message.includes('No matching export')) throw error
    console.log(`The control does not export all of ${names.join('+')}.`)
    control = new Map()
  }
  const before = new Map([...control].map(([name, bytes]) => [name, [bytes]]))
  return sizeTable(rows, ['Module', 'Bytes'], before)
}

async function main(config: Config): Promise<number> {
  writeJson(path.join(config.directory, 'plan.json'), {
    modules: config.modules ?? null,
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
