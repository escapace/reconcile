/**
 * Consumer bundle review (`pnpm bench size`).
 *
 * Bundles every nonempty combination of the six operations, and each other runtime export on
 * its own, from the built ESM entry point with esbuild, minified for a browser ES2022 target,
 * then reports minified and gzip (level 9) sizes. It checks
 * that the package's top-level code is removable (an import that uses nothing emits no
 * JavaScript even when the package's `sideEffects: false` is ignored), smoke-tests each bundle,
 * and writes `sizes.json`. Published source size does not measure consumer tree shaking; this
 * script measures the bundles consumers actually ship.
 *
 * Usage:
 *   pnpm build && pnpm bench size [--entry lib/neutral/index.js] [--out directory]
 *     [--compare sizes.json] [--no-smoke]
 */

import assert from 'node:assert/strict'
import { createHash } from 'node:crypto'
import {
  existsSync,
  mkdirSync,
  mkdtempSync,
  readdirSync,
  readFileSync,
  statSync,
  writeFileSync,
} from 'node:fs'
import { tmpdir } from 'node:os'
import path from 'node:path'
import { pathToFileURL } from 'node:url'
import { parseArgs } from 'node:util'
import { gzipSync } from 'node:zlib'
import { loadEsbuild } from './esbuild'

const ROOT = path.resolve(import.meta.dirname, '..')
const OPERATIONS = [
  'snapshot',
  'reconcile',
  'produce',
  'serialize',
  'deserialize',
  'requiredMaxBytes',
] as const
const OTHERS = [
  'isReconcileError',
  'isReconcileErrorOfType',
  'RECONCILE_ERROR_TYPES',
  'ReconcileError',
] as const
const usage =
  'Usage: pnpm bench size [--entry lib/neutral/index.js] [--out directory]\n' +
  '  [--compare sizes.json] [--no-smoke]'

const { values } = parseArgs({
  allowNegative: true,
  options: {
    compare: { type: 'string' },
    entry: { default: 'lib/neutral/index.js', type: 'string' },
    help: { short: 'h', type: 'boolean' },
    out: { type: 'string' },
    smoke: { default: true, type: 'boolean' },
  },
})
if (values.help === true) {
  console.log(usage)
  process.exit(0)
}

const esbuild = loadEsbuild()
const entry = path.resolve(ROOT, values.entry)
const options = {
  bundle: true,
  format: 'esm',
  minify: true,
  platform: 'browser',
  target: 'es2022',
  write: false,
}

interface Row {
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

/** Fails when an input of the entry's own build is newer than it: the sizes would be stale. */
function assertFresh(): void {
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
async function assertRemovable(): Promise<void> {
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

async function smoke(sources: Map<string, Uint8Array>): Promise<void> {
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

const number = (value: number): string => value.toLocaleString('en-US')
const percent = (before: number, after: number): string =>
  `${after >= before ? '+' : ''}${((100 * (after - before)) / before).toFixed(2)}%`

interface Sizes {
  readonly rows: Row[]
  readonly esbuild?: string
}

function sizeLine(row: Row, old: Row | undefined): string {
  if (old === undefined)
    return `| \`${row.name}\` | new → ${number(row.minified)} | | new → ${number(row.gzip)} | |`
  return (
    `| \`${row.name}\` | ${number(old.minified)} → ${number(row.minified)} | ` +
    `${percent(old.minified, row.minified)} | ${number(old.gzip)} → ${number(row.gzip)} | ` +
    `${percent(old.gzip, row.gzip)} |`
  )
}

/** The size table against a previous `sizes.json`, with new and removed rows. */
function compareTable(rows: Row[], previous: Sizes): string[] {
  const before = new Map(previous.rows.map((row) => [row.name, row]))
  const lines = [
    '| Exports | Minified before → after | Change | Gzip before → after | Change |',
    '| --- | ---: | ---: | ---: | ---: |',
  ]
  if (previous.esbuild !== esbuild.version)
    lines.unshift(`Note: esbuild ${previous.esbuild} before, ${esbuild.version} now.\n`)
  for (const row of rows) {
    lines.push(sizeLine(row, before.get(row.name)))
    before.delete(row.name)
  }
  for (const name of before.keys()) lines.push(`| \`${name}\` | removed | | removed | |`)
  return lines
}

const plainTable = (rows: Row[]): string[] => [
  '| Exports | Minified | Gzip |',
  '| --- | ---: | ---: |',
  ...rows.map((row) => `| \`${row.name}\` | ${number(row.minified)} | ${number(row.gzip)} |`),
]

assertFresh()
await assertRemovable()
const outputDirectory = path.resolve(
  values.out ?? mkdtempSync(path.join(tmpdir(), 'reconcile-bundles-')),
)
mkdirSync(outputDirectory, { recursive: true })
const rows: Row[] = []
const sources = new Map<string, Uint8Array>()
for (const names of selections()) {
  const bytes = await bundle(`export {${names.join(',')}} from ${JSON.stringify(entry)}`)
  const name = names.join('+')
  writeFileSync(path.join(outputDirectory, `${name}.js`), bytes)
  sources.set(name, bytes)
  rows.push({ gzip: gzipSync(bytes, { level: 9 }).length, minified: bytes.length, name })
}
if (values.smoke) await smoke(sources)
const previous =
  values.compare === undefined
    ? undefined
    : (JSON.parse(readFileSync(path.resolve(ROOT, values.compare), 'utf8')) as Sizes)
const lines = previous === undefined ? plainTable(rows) : compareTable(rows, previous)
writeFileSync(
  path.join(outputDirectory, 'sizes.json'),
  JSON.stringify(
    {
      entry: values.entry,
      entrySha256: createHash('sha256').update(readFileSync(entry)).digest('hex'),
      esbuild: esbuild.version,
      rows,
      smoke: values.smoke,
    },
    null,
    2,
  ) + '\n',
)
console.log(lines.join('\n'))
console.log(`\nBundles and sizes.json written to ${outputDirectory}`)
