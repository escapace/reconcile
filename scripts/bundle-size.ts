/**
 * Consumer bundle review.
 *
 * Bundles every nonempty export combination of the built ESM entry point with esbuild,
 * minified for a browser ES2020 target with peer dependencies included, then reports
 * minified and gzip (level 9) sizes, checks that an unused import emits no JavaScript, and
 * smoke-tests each bundle's available APIs. Published source size does not measure consumer
 * tree shaking; this script measures the bundles consumers actually ship.
 *
 * Usage:
 *   pnpm build && pnpm exec tsx scripts/bundle-size.ts [--entry lib/neutral/index.js]
 *     [--out directory] [--compare sizes.json] [--no-smoke]
 */

import assert from 'node:assert/strict'
import { mkdirSync, mkdtempSync, readdirSync, readFileSync, writeFileSync } from 'node:fs'
import { createRequire } from 'node:module'
import { tmpdir } from 'node:os'
import path from 'node:path'
import { parseArgs } from 'node:util'
import { gzipSync } from 'node:zlib'

const ROOT = path.resolve(import.meta.dirname, '..')
const require = createRequire(import.meta.url)
const NAMES = ['snapshot', 'reconcile', 'produce'] as const

const { values } = parseArgs({
  options: {
    compare: { type: 'string' },
    entry: { default: 'lib/neutral/index.js', type: 'string' },
    out: { type: 'string' },
    smoke: { default: true, type: 'boolean' },
  },
})

const esbuildPath = (() => {
  const pnpmDirectory = path.join(ROOT, 'node_modules', '.pnpm')
  const candidate = readdirSync(pnpmDirectory).find((directory) => directory.startsWith('esbuild@'))
  if (candidate === undefined) throw new Error('esbuild not found in pnpm store')
  return path.join(pnpmDirectory, candidate, 'node_modules', 'esbuild')
})()
const esbuild = require(esbuildPath) as {
  version: string
  build: (options: Record<string, unknown>) => Promise<{
    metafile: unknown
    outputFiles: Array<{ contents: Uint8Array }>
  }>
}

interface Row {
  gzip: number
  minified: number
  name: string
}

const outputDirectory =
  values.out === undefined
    ? mkdtempSync(path.join(tmpdir(), 'reconcile-bundles-'))
    : (mkdirSync(values.out, { recursive: true }), path.resolve(values.out))
const rows: Row[] = []
const sources = new Map<string, string>()
for (let mask = 0; mask < 8; mask += 1) {
  const names = NAMES.filter((_, index) => (mask & (1 << index)) !== 0)
  const result = await esbuild.build({
    bundle: true,
    format: 'esm',
    metafile: true,
    minify: true,
    platform: 'browser',
    stdin: {
      contents: `export {${names.join(',')}} from './${values.entry}'`,
      resolveDir: ROOT,
    },
    target: 'es2020',
    write: false,
  })
  const bytes = result.outputFiles[0].contents
  const name = names.length === 0 ? 'unused' : names.join('+')
  writeFileSync(path.join(outputDirectory, `${name}.js`), bytes)
  writeFileSync(
    path.join(outputDirectory, `${name}.meta.json`),
    JSON.stringify(result.metafile, null, 2),
  )
  sources.set(name, Buffer.from(bytes).toString('utf8'))
  rows.push({ gzip: gzipSync(bytes, { level: 9 }).length, minified: bytes.length, name })
}
assert.equal(rows[0].minified, 0, 'An unused import must emit no JavaScript.')

if (values.smoke) {
  for (const [name, code] of sources) {
    if (name === 'unused') continue
    const selected = name.split('+')
    const api = (await import(
      `data:text/javascript;base64,${Buffer.from(code).toString('base64')}`
    )) as Record<string, (...arguments_: unknown[]) => unknown>
    assert.deepEqual(Object.keys(api).sort(), selected.toSorted())
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
    if (api.snapshot !== undefined) {
      const copy = api.snapshot(base) as typeof base
      assert.notEqual(copy, base)
      assert.equal(copy.self, copy)
      assert.equal(copy.child, copy.alias)
      assert.notEqual(copy.child, child)
      assert.notEqual(copy.buffer, buffer)
      assert.equal((copy.view as Uint8Array).buffer, copy.buffer)
      assert.equal((copy.map as Map<string, unknown>).get('a'), copy.child)
      assert.ok((copy.set as Set<unknown>).has(copy.child))
    }
    if (api.produce !== undefined) {
      const next = api.produce(base, (draft: typeof base) => {
        ;(draft.child as { value: number }).value = 2
        return draft
      }) as typeof base
      assert.equal(child.value, 1)
      assert.equal((next.child as { value: number }).value, 2)
      assert.equal(next.alias, next.child)
      assert.equal(next.self, next)
    }
    if (api.reconcile !== undefined) {
      const current: Record<string, unknown> = { child: { value: 0 }, stale: true }
      const retained = current.child
      const next: Record<string, unknown> = { child: { value: 3 } }
      next.self = next
      assert.equal(api.reconcile(current, next), current)
      assert.equal(current.child, retained)
      assert.equal((current.child as { value: number }).value, 3)
      assert.equal(current.self, current)
      assert.ok(!('stale' in current))
    }
    if (api.snapshot !== undefined && api.reconcile !== undefined) {
      const target = api.snapshot(base) as typeof base
      assert.equal(api.reconcile(target, base), target)
      assert.equal(target.self, target)
      assert.equal(target.child, target.alias)
    }
    if (api.produce !== undefined && api.reconcile !== undefined) {
      const current = { value: 1 }
      const next = api.produce(current, (draft: typeof current) => {
        draft.value = 2
        return draft
      })
      assert.equal(api.reconcile(current, next), current)
      assert.equal(current.value, 2)
    }
    if (api.snapshot !== undefined && api.produce !== undefined) {
      const next = api.produce(api.snapshot(base), (draft: typeof base) => {
        ;(draft.child as { value: number }).value = 5
        return draft
      }) as typeof base
      assert.equal((next.child as { value: number }).value, 5)
      assert.equal(child.value, 1)
    }
  }
}

const previous =
  values.compare === undefined
    ? undefined
    : new Map(
        (JSON.parse(readFileSync(values.compare, 'utf8')) as { rows: Row[] }).rows.map((row) => [
          row.name,
          row,
        ]),
      )
const percent = (before: number, after: number): string =>
  `${after >= before ? '+' : ''}${((100 * (after - before)) / before).toFixed(2)}%`
const lines = [
  previous === undefined
    ? '| Exports | Minified | Gzip |\n| --- | ---: | ---: |'
    : '| Exports | Minified before → after | Gzip before → after | Gzip change |\n| --- | ---: | ---: | ---: |',
]
for (const row of rows.slice(1)) {
  const before = previous?.get(row.name)
  lines.push(
    before === undefined
      ? `| \`${row.name}\` | ${row.minified.toLocaleString('en-US')} | ${row.gzip.toLocaleString('en-US')} |`
      : `| \`${row.name}\` | ${before.minified.toLocaleString('en-US')} → ${row.minified.toLocaleString('en-US')} | ${before.gzip.toLocaleString('en-US')} → ${row.gzip.toLocaleString('en-US')} | ${percent(before.gzip, row.gzip)} |`,
  )
}
writeFileSync(
  path.join(outputDirectory, 'sizes.json'),
  JSON.stringify(
    { entry: values.entry, esbuild: esbuild.version, rows, smoke: values.smoke },
    null,
    2,
  ) + '\n',
)
console.log(lines.join('\n'))
console.log(`\nBundles and sizes.json written to ${outputDirectory}`)
