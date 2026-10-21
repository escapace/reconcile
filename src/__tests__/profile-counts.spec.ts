import { expect, it } from 'vitest'
import { readdirSync, readFileSync } from 'node:fs'
import path from 'node:path'
import { runInNewContext } from 'node:vm'
import ts from 'typescript'
import { counterReport, counterSetup, instrumentCounts } from '../../scripts/profile-counts'

function prepare(source: string, path = 'src/types/fixture.ts') {
  const overlay = instrumentCounts(source, path)
  const counts: Record<string, number> = {}
  const exports: { run?: (value: object) => unknown } = {}
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

it.each(['src/types/fixture.ts', 'src/draft-session.ts', 'src/finalization.ts'])(
  'preserves the getter and method receiver in native owner %s',
  (path) => {
    let reads = 0
    const value = {
      get constructor() {
        reads += 1
        return function (this: object) {
          return this
        }
      },
    }
    const { counts, run } = prepare(
      'export function run(value: any) { return value.constructor() }',
      path,
    )
    expect(run(value)).toBe(value)
    expect(reads).toBe(1)
    expect(counts['native.member.constructor']).toBe(1)
  },
)

it('counts current registry predicates only when their recognition branch is reached', () => {
  const { counts, run } = prepare(
    `export function run(value: any) {
      for (const module of value) {
        if (module.recognition.tag === 'fallback' || module.recognition.test(value)) return true
      }
      return false
    }`,
    'src/types/registry.ts',
  )
  expect(run([{ recognition: { tag: 'predicate', test: () => true } }])).toBe(true)
  expect(counts['classification.predicateTests']).toBe(1)
  expect(run([{ recognition: { tag: 'fallback' } }])).toBe(true)
  expect(counts['classification.predicateTests']).toBe(1)
})

it('does not execute a native read hidden behind a short circuit', () => {
  const value = {
    get buffer() {
      throw new Error('must not read')
    },
  }
  const { counts, run, sites } = prepare(
    'export function run(value: any) { return false && value.buffer }',
  )
  expect(run(value)).toBe(false)
  expect(counts['native.member.buffer']).toBeUndefined()
  expect(sites['native.member.buffer']).toBe(1)
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

it.each(['new Set([...state.checked, 9])', 'new Set(state.checked)'])(
  'counts actual checked entries in %s without extra native reads',
  (expression) => {
    let reads = 0
    let iterations = 0
    let report = ''
    const state = {
      get checked() {
        reads += 1
        return {
          *[Symbol.iterator]() {
            iterations += 1
            yield 3
            yield 7
          },
        }
      },
    }
    const overlay = instrumentCounts(
      `export function run(state: any) { return ${expression} }`,
      'src/graph/execution.ts',
    )
    const result = runInNewContext(
      counterSetup +
        ts.transpileModule(overlay.contents, {
          compilerOptions: { module: ts.ModuleKind.CommonJS, target: ts.ScriptTarget.ES2022 },
        }).outputText +
        '\nconst result = exports.run(state)\n' +
        counterReport +
        '\nresult',
      { console: { log: (line: string) => (report = line) }, exports: {}, state },
    ) as Set<number>
    expect([...result]).toEqual(expression.includes('9') ? [3, 7, 9] : [3, 7])
    expect(reads).toBe(1)
    expect(iterations).toBe(1)
    expect(JSON.parse(report.slice('RECONCILE_COUNTS '.length))).toMatchObject({
      'execution.checkedEntriesCopied': 2,
    })
    expect(overlay.sites['execution.checkedEntriesCopied']).toBe(1)
  },
)

it('audits zero-copy checked access and refuses an unrecognized use', () => {
  const path = 'src/graph/execution.ts'
  expect(
    instrumentCounts('state.checked.add(1); state.checked.has(1); state.checked.size', path).sites[
      'execution.checkedEntriesCopied'
    ],
  ).toBe(0)
  expect(() => instrumentCounts('consume(state.checked)', path)).toThrow(
    'Unaudited checked-store access',
  )
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

it('counts current incoming-summary queries without comparisons after an empty summary', () => {
  const { counts, run } = prepare(
    `export function run(value: any) {
      const incoming = value.incoming
      const event = { exposed: value.exposed }
      return incoming !== undefined && incoming !== event.exposed
    }`,
    'src/graph/execution.ts',
  )
  expect(run({ exposed: 1, incoming: undefined })).toBe(false)
  expect(counts['execution.incomingQueries']).toBe(1)
  expect(counts['execution.incomingSummaryComparisons']).toBeUndefined()
  expect(run({ exposed: 1, incoming: 2 })).toBe(true)
  expect(counts['execution.incomingQueries']).toBe(2)
  expect(counts['execution.incomingSummaryComparisons']).toBe(1)
})

it('counts forced assignments and restoration without changing indexed storage', () => {
  const { counts, run } = prepare(
    `
    export function run(value: any) {
      const forced: any[] = [], group = [{ node: 0 }, { node: 2, choice: 7 }]
      const member = 1
      forced![group[member].node] = group[member].choice
      const selected = forced[2]
      forced![group[member].node] = undefined
      return [selected, forced[2]]
    }`,
    'src/graph/selection.ts',
  )
  expect(Array.from(run({}) as unknown[])).toEqual([7, undefined])
  expect(counts['selection.forceWrites']).toBe(1)
  expect(counts['selection.forceRestores']).toBe(1)
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
    'execution.incomingQueries',
    'execution.incomingSummaryComparisons',
    'execution.incomingSummaryUpdates',
    'selection.activeQueries',
    'selection.choiceChecks',
    'selection.forceRestores',
    'selection.forceWrites',
    'selection.groupScanEdges',
    'selection.plans',
    'selection.supportDeletions',
    'selection.supportProbePositions',
    'selection.supportRequirementVisits',
    'selection.trailRestores',
    'selection.trailWrites',
    'storage.probes',
  ]
  expect(textMatched.filter((key) => !found.has(key))).toEqual([])
  expect([...(found.get('observation.events') ?? [])].toSorted()).toEqual([
    'src/finalization.ts',
    'src/publication/capture.ts',
  ])
})
