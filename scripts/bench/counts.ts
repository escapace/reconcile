import assert from 'node:assert/strict'
import { writeFileSync } from 'node:fs'
import path from 'node:path'
import ts from 'typescript'
import { entry } from '../framework/entry'
import { bundleHarness, record, runHarness, type Counting } from './harness'
import { inOverlay } from './scenarios'

const intrinsic = new Set([
  'Object.getOwnPropertyDescriptor',
  'Object.getPrototypeOf',
  'Object.isExtensible',
  'Reflect.get',
  'Reflect.ownKeys',
])

const FINALIZATION = 'src/finalization.ts'
const CANDIDATES = 'src/publication/candidates.ts'

/** The source file being instrumented. */
interface Site {
  readonly file: ts.SourceFile
  readonly path: string
}

/** Emits counter calls and records every emitted counter site. */
interface Counter {
  readonly factory: ts.NodeFactory
  readonly site: Site
  readonly sites: Record<string, number>
  /** Prepends one counter statement to a function body. */
  readonly prepend: (body: ts.Block, key: string, identity?: ts.Expression) => ts.Block
  readonly tally: (key: string, identity?: ts.Expression) => ts.Expression
  /** Evaluates one counter per key before the expression. */
  readonly wrap: (expression: ts.Expression, keys: string[]) => ts.Expression
}

type BinaryRule = (node: ts.BinaryExpression, file: ts.SourceFile) => string | undefined
type CallRule = (site: Site, node: ts.CallExpression, called: string) => string | undefined
/** Rewrites a visited node, or returns `undefined` when the rule does not apply. */
type Rewrite = (counter: Counter, node: ts.Node, updated: ts.Node) => ts.Node | undefined

function defined(keys: ReadonlyArray<string | undefined>): string[] {
  return keys.filter((key): key is string => key !== undefined)
}

/** Whether a call sits inside the per-phase kind memo (`kindOf` method or arrow). */
function insideKindMemo(node: ts.Node): boolean {
  for (let owner: ts.Node | undefined = node.parent; owner !== undefined; owner = owner.parent) {
    if (ts.isMethodDeclaration(owner)) return owner.name.getText() === 'kindOf'
    if (ts.isVariableDeclaration(owner) && ts.isIdentifier(owner.name))
      return owner.name.text === 'kindOf'
    if (ts.isFunctionDeclaration(owner)) return false
  }
  return false
}

/** The identifier a node is assigned to by its variable declaration, if any. */
function declaredIdentifier(node: ts.Node): string | undefined {
  return ts.isVariableDeclaration(node.parent) && ts.isIdentifier(node.parent.name)
    ? node.parent.name.text
    : undefined
}

const matchesText =
  (texts: string | readonly string[], key: string): BinaryRule =>
  (node, file) =>
    (typeof texts === 'string' ? [texts] : texts).includes(node.getText(file)) ? key : undefined

/** Binary expressions counted by their source text, per owning file. */
const binaryRules = new Map<string, BinaryRule[]>([
  [CANDIDATES, [matchesText('choices?.includes(object) === true', 'discovery.aliasVisits')]],
])

function binaryKeys(site: Site, node: ts.BinaryExpression): string[] {
  return defined((binaryRules.get(site.path) ?? []).map((rule) => rule(node, site.file)))
}

/** Calls in one file counted by their exact callee text. */
function exactCalls(path: string, entries: ReadonlyArray<[called: string, key: string]>): CallRule {
  const keys = new Map(entries)
  return (site, _node, called) => (site.path === path ? keys.get(called) : undefined)
}

const intrinsicCall: CallRule = (_site, _node, called) =>
  intrinsic.has(called) ? `native.${called}` : undefined

const kindMemoMiss: CallRule = (site, node, called) =>
  [CANDIDATES, FINALIZATION].includes(site.path) && called === 'recognize' && insideKindMemo(node)
    ? 'classification.memoMiss'
    : undefined

/** Call-site counters, in emission order. */
const callRules: CallRule[] = [
  exactCalls('src/types/builtins.ts', [
    ['Array.isArray', 'classification.predicateTests'],
    ['inChain', 'classification.predicateTests'],
    ['ArrayBuffer.isView', 'classification.predicateTests'],
    ['temporal.temporalInChain', 'classification.predicateTests'],
  ]),
  intrinsicCall,
  kindMemoMiss,
  exactCalls(FINALIZATION, [['this.untrackedSpecialsToClone.add', 'semantic.activations']]),
]

function callKeys(site: Site, node: ts.CallExpression): string[] {
  const called = node.expression.getText(site.file)
  return defined(callRules.map((rule) => rule(site, node, called)))
}

/** Graph record literals recognized by the identifier names they define. */
const literalShapes: ReadonlyArray<[key: string, names: string[]]> = [
  ['graph.candidateLiteral', ['identity', 'required']],
  ['graph.capturedNodeLiteral', ['edges', 'keys', 'layout']],
  ['graph.reuseNodeLiteral', ['children', 'layout', 'target']],
]
const edgeOwners = [CANDIDATES, 'src/publication/capture.ts', 'src/restore-identities.ts']

function propertyNames(node: ts.ObjectLiteralExpression): Set<string> {
  return new Set(
    node.properties.flatMap((property) =>
      property.name !== undefined && ts.isIdentifier(property.name) ? [property.name.text] : [],
    ),
  )
}

function isEdgeLiteral(path: string, names: ReadonlySet<string>): boolean {
  return edgeOwners.includes(path) && names.size === 1 && (names.has('node') || names.has('value'))
}

function objectKeys(site: Site, node: ts.ObjectLiteralExpression): string[] {
  const names = propertyNames(node)
  return defined([
    'allocation.objectLiteral',
    ...literalShapes.map(([key, required]) =>
      required.every((name) => names.has(name)) ? key : undefined,
    ),
    isEdgeLiteral(site.path, names) ? 'graph.edgeLiteral' : undefined,
  ])
}

/** Counter keys for an expression, in emission order. */
function counterKeys(site: Site, node: ts.Node): string[] {
  if (ts.isBinaryExpression(node)) return binaryKeys(site, node)
  if (ts.isCallExpression(node)) return callKeys(site, node)
  if (ts.isObjectLiteralExpression(node)) return objectKeys(site, node)
  if (ts.isArrayLiteralExpression(node)) return ['allocation.arrayLiteral']
  if (ts.isNewExpression(node)) return [`allocation.new.${node.expression.getText(site.file)}`]
  return []
}

function prependToArrow(
  counter: Counter,
  updated: ts.ArrowFunction,
  body: ts.Block,
  key: string,
): ts.ArrowFunction {
  return counter.factory.updateArrowFunction(
    updated,
    updated.modifiers,
    updated.typeParameters,
    updated.parameters,
    updated.type,
    updated.equalsGreaterThanToken,
    counter.prepend(body, key),
  )
}

/** Function-entry counters by owning file and function name. */
const entryTallies = new Map<string, ReadonlyMap<string, string>>([
  [
    'src/adapters/recognition.ts',
    new Map([
      ['matchesKind', 'classification.expected'],
      ['recognize', 'classification.full'],
      ['recognizeStructure', 'classification.full'],
    ]),
  ],
  ['src/types/shared/property-publication.ts', new Map([['propertySlots', 'shape.indexBuilds']])],
])
/** Entry counters that also count distinct `value` arguments. */
const identityTallies = new Set(['classification.expected', 'classification.full'])

function entryKey(path: string, name: string | undefined): string | undefined {
  return name === undefined ? undefined : entryTallies.get(path)?.get(name)
}

const countFunctionEntry: Rewrite = (counter, _node, updated) => {
  if (!ts.isFunctionDeclaration(updated) || updated.body === undefined) return undefined
  const key = entryKey(counter.site.path, updated.name?.text)
  if (key === undefined) return undefined
  const f = counter.factory
  return f.updateFunctionDeclaration(
    updated,
    updated.modifiers,
    updated.asteriskToken,
    updated.name,
    updated.typeParameters,
    updated.parameters,
    updated.type,
    counter.prepend(
      updated.body,
      key,
      identityTallies.has(key) ? f.createIdentifier('value') : undefined,
    ),
  )
}

/** Finalization keeps its recognition memo in a `kindOf` method. */
const countMethodMemo: Rewrite = (counter, _node, updated) => {
  if (
    !ts.isMethodDeclaration(updated) ||
    updated.body === undefined ||
    counter.site.path !== FINALIZATION ||
    updated.name.getText(counter.site.file) !== 'kindOf'
  )
    return undefined
  return counter.factory.updateMethodDeclaration(
    updated,
    updated.modifiers,
    updated.asteriskToken,
    updated.name,
    updated.questionToken,
    updated.typeParameters,
    updated.parameters,
    updated.type,
    counter.prepend(updated.body, 'classification.memoLookups'),
  )
}

/** Candidate discovery keeps its recognition memo in a local arrow named like the method. */
const countArrowMemo: Rewrite = (counter, node, updated) => {
  if (
    !ts.isArrowFunction(updated) ||
    !ts.isBlock(updated.body) ||
    counter.site.path !== CANDIDATES ||
    declaredIdentifier(node) !== 'kindOf'
  )
    return undefined
  return prependToArrow(counter, updated, updated.body, 'classification.memoLookups')
}

/** Callbacks passed as the second or third argument of `observe` or `observeDraft`. */
function isObserveCallback(node: ts.ArrowFunction): boolean {
  const call = node.parent
  return (
    ts.isCallExpression(call) &&
    ts.isPropertyAccessExpression(call.expression) &&
    ['observe', 'observeDraft'].includes(call.expression.name.text) &&
    // TypeScript AST arguments, not the legacy Function.arguments property.
    // eslint-disable-next-line baseline-js/use-baseline
    (call.arguments[1] === node || call.arguments[2] === node)
  )
}

/** Whether an arrow is an observation callback in a file that observes application objects. */
function isObservation(site: Site, node: ts.ArrowFunction): boolean {
  return (
    [FINALIZATION, 'src/publication/capture.ts'].includes(site.path) &&
    // The traversal hoists its begin/edge observation callbacks out of the per-node scope.
    (isObserveCallback(node) || ['begin', 'edge'].includes(declaredIdentifier(node) ?? ''))
  )
}

const countObservation: Rewrite = (counter, node, updated) => {
  if (
    !ts.isArrowFunction(updated) ||
    !ts.isArrowFunction(node) ||
    !ts.isBlock(updated.body) ||
    !isObservation(counter.site, node)
  )
    return undefined
  return prependToArrow(counter, updated, updated.body, 'observation.events')
}

/** Finalization observes through the `begin` and `edge` methods of its `DraftObservation`. */
const countObservationMethod: Rewrite = (counter, node, updated) => {
  if (
    !ts.isMethodDeclaration(updated) ||
    updated.body === undefined ||
    counter.site.path !== FINALIZATION ||
    !['begin', 'edge'].includes(updated.name.getText(counter.site.file)) ||
    !ts.isClassDeclaration(node.parent) ||
    node.parent.name?.text !== 'DraftObservation'
  )
    return undefined
  return counter.factory.updateMethodDeclaration(
    updated,
    updated.modifiers,
    updated.asteriskToken,
    updated.name,
    updated.questionToken,
    updated.typeParameters,
    updated.parameters,
    updated.type,
    counter.prepend(updated.body, 'observation.events'),
  )
}

/** Statement-level rewrites; the first that applies wins. */
const rewrites: Rewrite[] = [
  countFunctionEntry,
  countMethodMemo,
  countArrowMemo,
  countObservation,
  countObservationMethod,
]

function rewrite(counter: Counter, node: ts.Node, updated: ts.Node): ts.Node | undefined {
  for (const rule of rewrites) {
    const result = rule(counter, node, updated)
    if (result !== undefined) return result
  }
  return undefined
}

function createCounter(
  context: ts.TransformationContext,
  site: Site,
  sites: Record<string, number>,
): Counter {
  const f = context.factory
  const tally = (key: string, identity?: ts.Expression): ts.Expression => {
    sites[key] = (sites[key] ?? 0) + 1
    return f.createCallChain(
      f.createPropertyAccessExpression(f.createIdentifier('globalThis'), '__reconcileCount'),
      f.createToken(ts.SyntaxKind.QuestionDotToken),
      undefined,
      [f.createStringLiteral(key), ...(identity === undefined ? [] : [identity])],
    )
  }
  return {
    factory: f,
    site,
    sites,
    tally,
    prepend: (body, key, identity) =>
      f.updateBlock(body, [f.createExpressionStatement(tally(key, identity)), ...body.statements]),
    wrap: (expression, keys) =>
      keys.length === 0
        ? expression
        : f.createParenthesizedExpression(
            f.createCommaListExpression([...keys.map((key) => tally(key)), expression]),
          ),
  }
}

/** Diagnostic-only TypeScript overlay. Counters add no application property reads. */
export function instrumentCounts(source: string, path: string) {
  const file = ts.createSourceFile(path, source, ts.ScriptTarget.Latest, true, ts.ScriptKind.TS)
  const site: Site = { file, path }
  const sites: Record<string, number> = {}
  const transformed = ts.transform(file, [
    (context) => {
      const counter = createCounter(context, site, sites)
      const visit: ts.Visitor = (node) => {
        const updated = ts.visitEachChild(node, visit, context)
        const keys = counterKeys(site, node)
        if (ts.isExpression(updated) && keys.length !== 0) return counter.wrap(updated, keys)
        return rewrite(counter, node, updated) ?? updated
      }
      return (root) => ts.visitNode(root, visit) as ts.SourceFile
    },
  ])
  const contents = ts.createPrinter().printFile(transformed.transformed[0])
  transformed.dispose()
  return { contents, sites }
}

const counterSetup = `
let diagnosticCounts = Object.create(null)
let diagnosticIdentities = Object.create(null)
globalThis.__reconcileCount = (key, identity) => {
  diagnosticCounts[key] = (diagnosticCounts[key] ?? 0) + 1
  if (identity !== undefined) {
    const seen = diagnosticIdentities[key] ??= new WeakMap()
    const previous = seen.get(identity) ?? 0
    seen.set(identity, previous + 1)
    if (previous === 0) diagnosticCounts[key + '.identities'] = (diagnosticCounts[key + '.identities'] ?? 0) + 1
    diagnosticCounts[key + '.maximumPerIdentity'] = Math.max(diagnosticCounts[key + '.maximumPerIdentity'] ?? 0, previous + 1)
  }
}
`
const counterReset =
  'diagnosticCounts = Object.create(null)\ndiagnosticIdentities = Object.create(null)\n'
const counterReport = "console.log('RECONCILE_COUNTS ' + JSON.stringify(diagnosticCounts))\n"

type Counts = Record<string, number>

const IDENTITY_COUNTERS = ['classification.full', 'classification.expected']

/** Instrumented sites that never ran still report zero. */
function zeroFillSites(counts: Counts, counterSites: Record<string, Counts>): void {
  for (const sites of Object.values(counterSites))
    for (const key of Object.keys(sites)) counts[key] ??= 0
}

function assertCounters(counts: Counts): void {
  for (const count of Object.values(counts))
    assert(Number.isSafeInteger(count) && count >= 0, 'Invalid counter')
}

function addMemoHits(counts: Counts): void {
  if ('classification.memoLookups' in counts && 'classification.memoMiss' in counts) {
    counts['classification.memoHits'] =
      counts['classification.memoLookups'] - counts['classification.memoMiss']
    assert(counts['classification.memoHits'] >= 0)
  }
}

function zeroFillIdentity(counts: Counts, key: string): void {
  counts[`${key}.identities`] ??= 0
  counts[`${key}.maximumPerIdentity`] ??= 0
}

export function countsResult(
  counts: Record<string, number>,
  counterSites: Record<string, Record<string, number>>,
  operations: number,
) {
  zeroFillSites(counts, counterSites)
  assertCounters(counts)
  addMemoHits(counts)
  for (const key of IDENTITY_COUNTERS) if (key in counts) zeroFillIdentity(counts, key)
  return {
    counts,
    operations,
    scope:
      'Exact instrumented events; allocation counters describe source constructions, not physical V8 allocations. Counting time is not throughput.',
  }
}

/** The counters whose counts differ between two runs, as `[control, tree]`; a counter one run
 * lacks is `null` there. */
export function countChanges(
  control: Record<string, number>,
  tree: Record<string, number>,
): Record<string, [number | null, number | null]> {
  const names = [...new Set([...Object.keys(control), ...Object.keys(tree)])].toSorted()
  return Object.fromEntries(
    names
      .filter((name) => control[name] !== tree[name])
      .map((name) => [name, [control[name] ?? null, tree[name] ?? null]]),
  )
}

/** The counting overlay the harness bundles. */
const COUNTING: Counting = {
  instrument: instrumentCounts,
  report: counterReport,
  reset: counterReset,
  setup: counterSetup,
}

/** The configuration `pnpm bench counts` passes. */
interface Config {
  readonly batches: number
  /** The control's source tree, to compare with. */
  readonly control: string | undefined
  readonly directory: string
  readonly scenarios: readonly string[]
  readonly size: number
  readonly tree: string
  readonly warmup: number
}

/** Counts one scenario on one tree, keeping the bundle, the instrumented sources and the log. */
async function count(config: Config, scenario: string, tree: string, directory: string) {
  const harness = await bundleHarness({
    counting: COUNTING,
    directory,
    overlay: inOverlay(scenario),
    size: config.size,
    tree,
  })
  const output = runHarness(
    {
      batches: config.batches,
      bundle: harness.bundlePath,
      log: path.join(directory, 'run.log'),
      scenario,
      warmup: config.warmup,
    },
    tree,
  )
  const counts = record(output, 'RECONCILE_COUNTS ') as Counts
  // Each tree's harness reports the operations it ran, by its own frozen batch size.
  const { operations } = record(output, 'RECONCILE_TIME ') as { operations: number }
  const result = countsResult(counts, harness.counterSites, operations)
  writeFileSync(path.join(directory, 'counts.json'), `${JSON.stringify(result, undefined, 2)}\n`)
  return result
}

/** Counts each scenario on the tree and, with a control, reports the counters that differ;
 * counts are exact, so one run per tree decides. */
async function main(config: Config): Promise<number> {
  for (const scenario of config.scenarios) {
    const tree = await count(
      config,
      scenario,
      config.tree,
      path.join(config.directory, scenario, 'tree'),
    )
    if (config.control === undefined) {
      console.log(`${scenario}: ${JSON.stringify(tree, undefined, 2)}`)
      continue
    }
    const control = await count(
      config,
      scenario,
      config.control,
      path.join(config.directory, scenario, 'control'),
    )
    const changed = countChanges(control.counts, tree.counts)
    const comparison = {
      changed,
      operations: tree.operations,
      trees: { control: config.control, tree: config.tree },
    }
    writeFileSync(
      path.join(config.directory, scenario, 'comparison.json'),
      `${JSON.stringify(comparison, undefined, 2)}\n`,
    )
    const names = Object.keys(changed)
    console.log(
      names.length === 0
        ? `${scenario}: every counter equals the control's`
        : `${scenario}: ${names.length} counters differ, as [control, tree]: ${JSON.stringify(changed, undefined, 2)}`,
    )
  }
  return 0
}

await entry(import.meta.filename, main)
