import { build, type BuildOptions } from 'esroll'
import { readFile } from 'node:fs/promises'
import path from 'node:path'

const dirname = path.resolve(import.meta.dirname, '../')
process.chdir(dirname)

const constants = JSON.parse(
  await readFile(path.join(import.meta.dirname, 'constants.json'), 'utf-8'),
) as {
  builds: Record<string, { mangle?: string[] } & BuildOptions>
  declaration?: BuildOptions
}

for (const { mangle, ...value } of Object.values(constants.builds)) {
  await build({
    // Internal protocol and facet member names are renamed in the published bundle. The
    // allowlist contains no name that the library reads on application or native objects
    // (descriptor fields, collection methods, Proxy traps and `in` keys stay).
    // Ordinary consumer minification does not rename properties; see docs/development.md.
    ...(mangle === undefined ? {} : { mangleProps: new RegExp(`^(?:${mangle.join('|')})$`) }),
    sourcemap: true,
    sourcesContent: false,
    treeShaking: true,
    tsconfig: 'tsconfig-build.json',
    ...value,
    absWorkingDir: dirname,
  })
}

if (constants.declaration !== undefined) {
  await build({
    declaration: true,
    ...constants.declaration,
  })
}
