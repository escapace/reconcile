// Builds the package with Rolldown: the library as one ES2022 module in `lib/neutral`, its
// internal member names renamed, and its declarations, emitted by TypeScript 7 and rolled into
// `lib/types/index.d.ts` with their TSDoc comments.
import { readFile, rm, writeFile } from 'node:fs/promises'
import { createRequire } from 'node:module'
import path from 'node:path'
import { pathToFileURL } from 'node:url'
import { build } from 'rolldown'
import { dts } from 'rolldown-plugin-dts'

const root = path.resolve(import.meta.dirname, '..')
const entry = path.join(root, 'src', 'index.ts')

const { mangle } = JSON.parse(
  await readFile(path.join(import.meta.dirname, 'constants.json'), 'utf8'),
) as { mangle: string[] }

const packageDocumentation = /^\/\*\*(?:(?!\*\/)[\s\S])*@packageDocumentation[\s\S]*?\*\//.exec(
  await readFile(entry, 'utf8'),
)?.[0]
if (packageDocumentation === undefined)
  throw new Error(`${entry} does not open with its @packageDocumentation comment`)

/** The TypeScript 7 compiler, which the `@typescript/native` alias installs beside the
 * TypeScript 6 API that `typescript` names. */
async function typescript7(): Promise<string> {
  const manifest = createRequire(import.meta.url).resolve('@typescript/native/package.json')
  const locator = pathToFileURL(path.join(path.dirname(manifest), 'lib', 'getExePath.js')).href
  const { default: getExePath } = (await import(locator)) as { default: () => string }
  return getExePath()
}

await rm(path.join(root, 'lib', 'neutral'), { force: true, recursive: true })
await rm(path.join(root, 'lib', 'types'), { force: true, recursive: true })

await build({
  cwd: root,
  input: entry,
  output: {
    // Documentation comments are left out of the module; pure annotations and legal notices stay.
    comments: { annotation: true, jsdoc: false, legal: true },
    dir: path.join(root, 'lib', 'neutral'),
    format: 'esm',
    // Internal protocol and facet member names are renamed in the published bundle. The
    // allowlist contains no name that the library reads on application or native objects
    // (descriptor fields, collection methods, Proxy traps and `in` keys stay), and the rest of
    // the bundle stays readable. Ordinary consumer minification does not rename properties; see
    // docs/development.md.
    minify: {
      codegen: { removeWhitespace: false },
      compress: false,
      mangle: false,
      mangleProps: { include: new RegExp(`^(?:${mangle.join('|')})$`) },
    },
    sourcemap: true,
    sourcemapExcludeSources: true,
  },
  platform: 'neutral',
  transform: { target: 'es2022' },
  treeshake: true,
  tsconfig: path.join(root, 'tsconfig-build.json'),
})

await build({
  cwd: root,
  input: entry,
  output: { dir: path.join(root, 'lib', 'types'), format: 'esm' },
  platform: 'neutral',
  plugins: dts({
    emitDtsOnly: true,
    generator: 'tsgo',
    sourcemap: false,
    tsconfig: 'tsconfig-build.json',
    tsgo: { path: await typescript7() },
  }),
  tsconfig: path.join(root, 'tsconfig-build.json'),
})

// The declaration bundler drops the comment on the entry's first export, which documents the
// package; it is restored at the top.
const declarations = path.join(root, 'lib', 'types', 'index.d.ts')
await writeFile(declarations, `${packageDocumentation}\n\n${await readFile(declarations, 'utf8')}`)
