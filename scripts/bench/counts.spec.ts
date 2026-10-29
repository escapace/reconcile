import { expect, it } from 'vitest'
import { readdirSync, readFileSync } from 'node:fs'
import path from 'node:path'
import { runInNewContext } from 'node:vm'
import ts from 'typescript'
import { instrumentCounts } from './counts'

function prepare(source: string, path = 'src/types/fixture.ts') {
  const overlay = instrumentCounts(source, path)
  const counts: Record<string, number> = {}
  const exports: { run?: (this: unknown, value?: object) => unknown } = {}
  runInNewContext(
    ts.transpileModule(overlay.contents, {
      compilerOptions: { module: ts.ModuleKind.CommonJS },
    }).outputText,
    {
      exports,
      __reconcileCount: (key: string) => {
        counts[key] = (counts[key] ?? 0) + 1
      },
    },
  )
  return { counts, run: exports.run!, sites: overlay.sites }
}

it('preserves the getter and method receiver of a counted member call', () => {
  let reads = 0
  const holder = {
    get add() {
      reads += 1
      return function (this: object) {
        return this
      }
    },
  }
  const target = { untrackedSpecialsToClone: holder }
  const { counts, run } = prepare(
    'export function run(this: any) { return this.untrackedSpecialsToClone.add() }',
    'src/finalization.ts',
  )
  expect(run.call(target)).toBe(holder)
  expect(reads).toBe(1)
  expect(counts['semantic.activations']).toBe(1)
})

it('counts built-in recognition probes only when their branch is reached', () => {
  const { counts, run } = prepare(
    `export function run(value: any) {
      const inChain = value.inChain
      return value.plain || inChain(value.prototype)
    }`,
    'src/types/builtins.ts',
  )
  const probe = { plain: false, prototype: null, inChain: () => true }
  expect(run(probe)).toBe(true)
  expect(counts['classification.predicateTests']).toBe(1)
  expect(run({ ...probe, plain: true })).toBe(true)
  expect(counts['classification.predicateTests']).toBe(1)
})

it('counts source constructions and preserves a graph edge identity', () => {
  const { counts, run } = prepare(
    'export function run(value: any) { return { value } }',
    'src/publication/capture.ts',
  )
  const value = {}
  expect(run(value)).toEqual({ value })
  expect(counts).toEqual({ 'allocation.objectLiteral': 1, 'graph.edgeLiteral': 1 })
})

it('counts split begin and edge callbacks while preserving construction responses', () => {
  const { counts, run } = prepare(
    `export function run(value: any) {
      const policy = { observe(value: any, begin: any, edge: any) {
        begin(0)
        return edge(value, undefined, 5, true)
      } }
      return policy.observe(value, (layout: any) => { return layout },
        (child: any, key: any, kind: any, construction: any) => { return construction ? child : undefined })
    }`,
    'src/publication/capture.ts',
  )
  const value = {}
  expect(run(value)).toBe(value)
  expect(counts['observation.events']).toBe(2)
})

// Rules that find their call sites by exact source text drop their counter silently when the
// source changes, so each one must still match in the library.
it('finds a site in the library for every text-matched counter', () => {
  const root = path.resolve(import.meta.dirname, '../..')
  const files = readdirSync(path.join(root, 'src'), { encoding: 'utf8', recursive: true }).filter(
    (file) => file.endsWith('.ts') && !file.endsWith('.d.ts') && !file.startsWith('__tests__'),
  )
  const found = new Map<string, Set<string>>()
  for (const file of files) {
    const relative = `src/${file.split(path.sep).join('/')}`
    const { sites } = instrumentCounts(readFileSync(path.join(root, relative), 'utf8'), relative)
    for (const [key, count] of Object.entries(sites))
      if (count > 0) found.set(key, (found.get(key) ?? new Set()).add(relative))
  }
  const textMatched = [
    'classification.full',
    'classification.memoLookups',
    'classification.predicateTests',
    'discovery.aliasVisits',
  ]
  expect(textMatched.filter((key) => !found.has(key))).toEqual([])
  expect([...(found.get('observation.events') ?? [])].toSorted()).toEqual([
    'src/finalization.ts',
    'src/publication/capture.ts',
  ])
})
