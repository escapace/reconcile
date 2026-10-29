/**
 * The consumer bundles: every nonempty combination of the six operations, and each other runtime
 * export on its own, bundled from a built package with esbuild, minified for a browser ES2022
 * target, with their minified and gzip (level 9) sizes. Published source size does not measure
 * consumer tree shaking; these are the bundles consumers actually ship.
 *
 * Run by the `lib` round, it also checks that the package's top-level code is removable (an
 * import that uses nothing emits no JavaScript even when the package's `sideEffects: false` is
 * ignored) and smoke-tests each bundle; `pnpm bench size` compares the sizes.
 */

import assert from 'node:assert/strict'
import { createHash } from 'node:crypto'
import { existsSync, mkdirSync, readdirSync, readFileSync, statSync, writeFileSync } from 'node:fs'
import path from 'node:path'
import { pathToFileURL } from 'node:url'
import { gzipSync } from 'node:zlib'
import { loadEsbuild } from './esbuild'
import { entry as runEntry } from './framework/entry'
import { ROOT } from './framework/paths'

export const OPERATIONS = [
  'snapshot',
  'reconcile',
  'produce',
  'serialize',
  'deserialize',
  'requiredMaxBytes',
] as const
export const OTHERS = [
  'isReconcileError',
  'isReconcileErrorOfType',
  'RECONCILE_ERROR_TYPES',
  'ReconcileError',
] as const
const esbuild = loadEsbuild()
const options = {
  bundle: true,
  format: 'esm',
  minify: true,
  platform: 'browser',
  target: 'es2022',
  write: false,
}

export interface Row {
  gzip: number
  minified: number
  name: string
}

type Api = Record<string, (...arguments_: unknown[]) => unknown>

/** Errors carry their type in `cause`; class checks do not hold across separate bundles. */
const errorOfType = (type: string) => (error: unknown) =>
  (error as { cause?: { type?: string } }).cause?.type === type

/** The nearest directory above the entry with a `package.json`: the tree that built it. */
function packageRoot(file: string): string | undefined {
  for (let directory = path.dirname(file); ; directory = path.dirname(directory)) {
    if (existsSync(path.join(directory, 'package.json'))) return directory
    if (path.dirname(directory) === directory) return undefined
  }
}

/** The built package of a source tree. */
export const packageEntry = (tree: string): string => path.join(tree, 'lib', 'neutral', 'index.js')

/** Fails when an input of the entry's own build is newer than it: the sizes would be stale. */
export function assertFresh(entry: string): void {
  const root = packageRoot(entry)
  if (root === undefined || !existsSync(path.join(root, 'src'))) return
  const built = statSync(entry).mtimeMs
  const sources = readdirSync(path.join(root, 'src'), { recursive: true, withFileTypes: true })
    .filter((file) => file.isFile() && file.name.endsWith('.ts'))
    .map((file) => path.join(file.parentPath, file.name))
    .filter((file) => !file.includes(`${path.sep}__tests__${path.sep}`))
  const stale = [...sources, path.join(root, 'scripts', 'constants.json')]
    .filter((file) => existsSync(file))
    .find((file) => statSync(file).mtimeMs > built)
  assert.equal(stale, undefined, `${stale} is newer than ${entry}; build that tree first.`)
}

async function bundle(contents: string, plugins: unknown[] = []): Promise<Uint8Array> {
  const result = await esbuild.build({ ...options, plugins, stdin: { contents, resolveDir: ROOT } })
  return result.outputFiles[0].contents
}

/** Bundles `import entry` with `sideEffects` forced on: no top-level code may stay. */
async function assertRemovable(entry: string): Promise<void> {
  const keep = {
    name: 'keep-side-effects',
    setup(build: {
      onResolve: (
        options: { filter: RegExp },
        callback: (arguments_: { path: string; resolveDir: string }) => object,
      ) => void
    }) {
      const exact = new RegExp(`^${entry.replaceAll(/[$()*+.?[\\\]^{|}]/g, String.raw`\$&`)}$`)
      build.onResolve({ filter: exact }, (arguments_) => ({
        path: path.resolve(arguments_.resolveDir, arguments_.path),
        sideEffects: true,
      }))
    },
  }
  const bytes = await bundle(`import ${JSON.stringify(entry)}`, [keep])
  assert.equal(
    bytes.length,
    0,
    `The package keeps ${bytes.length} bytes of top-level code that no export uses; mark it pure.`,
  )
}

/** Every nonempty combination of the operations, then each other export alone. */
function selections(): string[][] {
  const combinations: string[][] = []
  for (let mask = 1; mask < 1 << OPERATIONS.length; mask += 1)
    combinations.push(OPERATIONS.filter((_, index) => (mask & (1 << index)) !== 0))
  return [...combinations, ...OTHERS.map((name) => [name])]
}

function graphFixture() {
  const buffer = new ArrayBuffer(16)
  const child = { value: 1 }
  const base: Record<string, unknown> = {
    alias: child,
    buffer,
    child,
    map: new Map([['a', child]]),
    set: new Set([child]),
    view: new Uint8Array(buffer),
  }
  base.self = base
  return { base, buffer, child }
}

type Fixtures = { full: Api; text: string } & ReturnType<typeof graphFixture>

/** Behavior each export must keep in a bundle of its own; a combination runs every check. */
const checks: Record<string, (api: Api, fixtures: Fixtures) => void> = {
  deserialize: (api, { text }) => {
    const copy = api.deserialize(JSON.parse(text), { maxBytes: 1024 }) as Record<string, unknown>
    assert.equal(copy.self, copy)
    assert.equal((copy.date as Date).getTime(), 7)
    assert.equal((copy.map as Map<string, unknown>).get('k'), 1n)
    assert.throws(
      () => api.deserialize({}, { maxBytes: 1024 }),
      errorOfType('DeserializeInputInvalid'),
    )
    assert.throws(
      () => api.deserialize(JSON.parse(text), { maxBytes: -1 }),
      errorOfType('DeserializeLimitInvalid'),
    )
  },
  isReconcileError: (api) => {
    assert.equal(api.isReconcileError(new Error('other')), false)
  },
  isReconcileErrorOfType: (api) => {
    const error = { cause: { reason: 'base64', type: 'DeserializeInputInvalid' } }
    assert.equal(api.isReconcileErrorOfType(error, 'DeserializeInputInvalid'), true)
    assert.equal(api.isReconcileErrorOfType(error, 'SerializeValueUnsupported'), false)
  },
  produce: (api, { base, child }) => {
    const next = api.produce(base, (draft: typeof base) => {
      ;(draft.child as { value: number }).value = 2
      return draft
    }) as typeof base
    assert.equal(child.value, 1)
    assert.equal((next.child as { value: number }).value, 2)
    assert.equal(next.alias, next.child)
    assert.equal(next.self, next)
  },
  reconcile: (api) => {
    const current: Record<string, unknown> = { child: { value: 0 }, stale: true }
    const retained = current.child
    const next: Record<string, unknown> = { child: { value: 3 } }
    next.self = next
    assert.equal(api.reconcile(current, next), current)
    assert.equal(current.child, retained)
    assert.equal((current.child as { value: number }).value, 3)
    assert.equal(current.self, current)
    assert.ok(!('stale' in current))
  },
  RECONCILE_ERROR_TYPES: (api) => {
    assert.ok(
      (api.RECONCILE_ERROR_TYPES as unknown as string[]).includes('DeserializeInputInvalid'),
    )
  },
  ReconcileError: (api) => {
    assert.equal(typeof api.ReconcileError, 'function')
  },
  requiredMaxBytes: (api, { full, text }) => {
    const json = JSON.parse(text) as unknown
    const maxBytes = api.requiredMaxBytes(json, { maxBytes: Infinity }) as number
    assert.equal(JSON.stringify(json), text)
    full.deserialize(json, { maxBytes })
    assert.throws(
      () => api.requiredMaxBytes(JSON.parse(text), { maxBytes: maxBytes - 1 }),
      errorOfType('DeserializeLimitExceeded'),
    )
    assert.throws(
      () => api.requiredMaxBytes({}, { maxBytes: 1024 }),
      errorOfType('DeserializeInputInvalid'),
    )
  },
  serialize: (api, { full, text }) => {
    const value = full.deserialize(JSON.parse(text), { maxBytes: Infinity })
    assert.equal(JSON.stringify(api.serialize(value)), text)
    assert.throws(() => api.serialize({ f: () => 1 }), errorOfType('SerializeValueUnsupported'))
  },
  snapshot: (api, { base, buffer, child }) => {
    const copy = api.snapshot(base) as typeof base
    assert.notEqual(copy, base)
    assert.equal(copy.self, copy)
    assert.equal(copy.child, copy.alias)
    assert.notEqual(copy.child, child)
    assert.notEqual(copy.buffer, buffer)
    assert.equal((copy.view as Uint8Array).buffer, copy.buffer)
    assert.equal((copy.map as Map<string, unknown>).get('a'), copy.child)
    assert.ok((copy.set as Set<unknown>).has(copy.child))
  },
}

async function smoke(entry: string, sources: ReadonlyMap<string, Uint8Array>): Promise<void> {
  const full = (await import(pathToFileURL(entry).href)) as Api
  const graph: Record<string, unknown> = { date: new Date(7), map: new Map([['k', 1n]]) }
  graph.self = graph
  const text = JSON.stringify(full.serialize(graph))
  for (const [name, code] of sources) {
    const selected = name.split('+')
    const api = (await import(
      `data:text/javascript;base64,${Buffer.from(code).toString('base64')}`
    )) as Api
    try {
      assert.deepEqual(Object.keys(api).toSorted(), selected.toSorted())
      for (const exported of selected) checks[exported](api, { ...graphFixture(), full, text })
    } catch (error) {
      throw new Error(`Smoke test failed for the ${name} bundle`, { cause: error })
    }
  }
}

/** Bundles every selection of the package at `entry` into `directory`, with its sizes. */
export async function bundleExports(
  entry: string,
  directory: string,
): Promise<{ rows: Row[]; sources: Map<string, Uint8Array> }> {
  mkdirSync(directory, { recursive: true })
  const rows: Row[] = []
  const sources = new Map<string, Uint8Array>()
  for (const names of selections()) {
    const bytes = await bundle(`export {${names.join(',')}} from ${JSON.stringify(entry)}`)
    const name = names.join('+')
    writeFileSync(path.join(directory, `${name}.js`), bytes)
    sources.set(name, bytes)
    rows.push({ gzip: gzipSync(bytes, { level: 9 }).length, minified: bytes.length, name })
  }
  writeFileSync(
    path.join(directory, 'sizes.json'),
    `${JSON.stringify({ entry, entrySha256: createHash('sha256').update(readFileSync(entry)).digest('hex'), esbuild: esbuild.version, rows }, undefined, 2)}\n`,
  )
  return { rows, sources }
}

const number = (value: number): string => value.toLocaleString('en-US')
const percent = (before: number, after: number): string =>
  `${after >= before ? '+' : ''}${((100 * (after - before)) / before).toFixed(2)}%`

/** A table of sizes, or of the change from `before` to `after` when there is a before. */
export function sizeTable(
  rows: ReadonlyArray<{ readonly name: string; readonly values: readonly number[] }>,
  headers: readonly string[],
  before?: ReadonlyMap<string, readonly number[]>,
): string {
  const lines =
    before === undefined
      ? [`| ${headers.join(' | ')} |`, `| --- |${' ---: |'.repeat(headers.length - 1)}`]
      : [
          `| ${headers[0]} | ${headers
            .slice(1)
            .flatMap((header) => [`${header} before → after`, 'Change'])
            .join(' | ')} |`,
          `| --- |${' ---: | ---: |'.repeat(headers.length - 1)}`,
        ]
  const names = new Set(before?.keys())
  for (const { name, values } of rows) {
    names.delete(name)
    const old = before?.get(name)
    const cells =
      before === undefined
        ? values.map(number)
        : values.flatMap((value, index) =>
            old === undefined
              ? [`new → ${number(value)}`, '']
              : [`${number(old[index])} → ${number(value)}`, percent(old[index], value)],
          )
    lines.push(`| \`${name}\` | ${cells.join(' | ')} |`)
  }
  for (const name of names)
    lines.push(
      `| \`${name}\` | ${headers
        .slice(1)
        .flatMap(() => ['removed', ''])
        .join(' | ')} |`,
    )
  return lines.join('\n')
}

/** The rows of a size table from bundle sizes. */
export const sizeRows = (rows: readonly Row[]) =>
  rows.map((row) => ({ name: row.name, values: [row.minified, row.gzip] }))

/** The `lib` round's bundle check: the package's top-level code is removable, and every bundle
 * keeps its exports' behavior. */
async function main({ directory }: { readonly directory: string }): Promise<number> {
  const entry = packageEntry(ROOT)
  assertFresh(entry)
  await assertRemovable(entry)
  const { rows, sources } = await bundleExports(entry, directory)
  await smoke(entry, sources)
  console.log(sizeTable(sizeRows(rows), ['Exports', 'Minified', 'Gzip']))
  console.log(`\nBundles and sizes.json written to ${directory}`)
  return 0
}

await runEntry(import.meta.filename, main)
