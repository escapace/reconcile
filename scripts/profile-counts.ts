import ts from 'typescript'

const intrinsic = new Set([
  'Object.getOwnPropertyDescriptor',
  'Object.getPrototypeOf',
  'Object.isExtensible',
  'Reflect.get',
  'Reflect.getOwnPropertyDescriptor',
  'Reflect.getPrototypeOf',
  'Reflect.isExtensible',
  'Reflect.ownKeys',
])
const metadata = new Set(['buffer', 'byteLength', 'byteOffset', 'constructor'])
const nativeOwners = new Set(['src/draft-session.ts', 'src/finalization.ts'])

const EXECUTION = 'src/graph/execution.ts'
const SELECTION = 'src/graph/selection.ts'
const SUPPORTED_CHOICES = 'src/graph/supported-choices.ts'
const FORCED_GROUPS = 'src/graph/forced-groups.ts'
const FINALIZATION = 'src/finalization.ts'
const CANDIDATES = 'src/publication/candidates.ts'

/** The source file being instrumented. */
interface Site {
  readonly file: ts.SourceFile
  /** Whether the file reads native-boundary metadata that the counters attribute. */
  readonly nativeOwner: boolean
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

function isAssignmentTo(node: ts.BinaryExpression, target: string, file: ts.SourceFile): boolean {
  return node.left.getText(file) === target && node.operatorToken.kind === ts.SyntaxKind.EqualsToken
}

/** Whether `state.checked` is copied entry by entry (spread or `new Set(state.checked)`). */
function copiesCheckedEntries(node: ts.PropertyAccessExpression, file: ts.SourceFile): boolean {
  const parent = node.parent
  return (
    ts.isSpreadElement(parent) ||
    (ts.isNewExpression(parent) &&
      parent.expression.getText(file) === 'Set' &&
      // TypeScript syntax-node fields, not legacy Function.arguments.
      // eslint-disable-next-line baseline-js/use-baseline
      parent.arguments?.length === 1 &&
      // eslint-disable-next-line baseline-js/use-baseline
      parent.arguments[0] === node)
  )
}

/** Counts copied checked-store entries; every other checked-store access must be audited. */
function countCheckedCopy(
  counter: Counter,
  node: ts.Node,
  updated: ts.Node,
): ts.Expression | undefined {
  const { file, path } = counter.site
  if (
    path !== EXECUTION ||
    !ts.isPropertyAccessExpression(node) ||
    node.getText(file) !== 'state.checked'
  )
    return undefined
  if (copiesCheckedEntries(node, file)) {
    counter.sites['execution.checkedEntriesCopied'] += 1
    const f = counter.factory
    return f.createCallExpression(
      f.createPropertyAccessExpression(
        f.createIdentifier('globalThis'),
        '__reconcileCheckedEntries',
      ),
      undefined,
      [updated as ts.Expression],
    )
  }
  const parent = node.parent
  if (!ts.isPropertyAccessExpression(parent) || !['add', 'has', 'size'].includes(parent.name.text))
    throw new Error(`Unaudited checked-store access: ${parent.getText(file)}`)
  return undefined
}

const matchesText =
  (text: string, key: string): BinaryRule =>
  (node, file) =>
    node.getText(file) === text ? key : undefined

/** Forced-follower slots restore with `undefined` and force with any other value. */
const forcedWrite: BinaryRule = (node, file) => {
  if (!isAssignmentTo(node, 'forced![group[member].node]', file)) return undefined
  return node.right.getText(file) === 'undefined'
    ? 'selection.forceRestores'
    : 'selection.forceWrites'
}

/** Binary expressions counted by their source text, per owning file. */
const binaryRules = new Map<string, BinaryRule[]>([
  [
    EXECUTION,
    [
      (node, file) =>
        isAssignmentTo(node, 'incoming[edge.node]', file)
          ? 'execution.incomingSummaryUpdates'
          : undefined,
      matchesText('incoming !== undefined', 'execution.incomingQueries'),
      matchesText('incoming !== event.exposed', 'execution.incomingSummaryComparisons'),
    ],
  ],
  [FORCED_GROUPS, [matchesText('edge.node <= node', 'selection.groupScanEdges')]],
  [
    SELECTION,
    [
      matchesText('choice !== undefined', 'selection.choiceChecks'),
      forcedWrite,
      matchesText('demand === undefined', 'selection.activeQueries'),
    ],
  ],
  [
    SUPPORTED_CHOICES,
    [
      matchesText('target.identity === edge.identity', 'selection.supportProbePositions'),
      matchesText('edge.node === node', 'selection.supportRequirementVisits'),
      matchesText('bucket.remaining === 0', 'selection.supportDeletions'),
    ],
  ],
])

function binaryKeys(site: Site, node: ts.BinaryExpression): string[] {
  return defined((binaryRules.get(site.path) ?? []).map((rule) => rule(node, site.file)))
}

/** Calls in one file counted by their exact callee text. */
function exactCalls(path: string, entries: ReadonlyArray<[called: string, key: string]>): CallRule {
  const keys = new Map(entries)
  return (site, _node, called) => (site.path === path ? keys.get(called) : undefined)
}

/** The member name of a native-owner method call, if any. */
function nativeMember(site: Site, callee: ts.Expression): string | undefined {
  return site.nativeOwner && ts.isPropertyAccessExpression(callee) ? callee.name.text : undefined
}

const metadataCall: CallRule = (site, node) => {
  const member = nativeMember(site, node.expression)
  return member !== undefined && metadata.has(member) ? `native.member.${member}` : undefined
}

const intrinsicCall: CallRule = (_site, _node, called) =>
  intrinsic.has(called) ? `native.${called}` : undefined

const kindMemoMiss: CallRule = (site, node, called) =>
  [CANDIDATES, FINALIZATION].includes(site.path) && called === 'recognize' && insideKindMemo(node)
    ? 'classification.memoMiss'
    : undefined

const dateTimeCall: CallRule = (site, node) =>
  nativeMember(site, node.expression) === 'getTime' ? 'native.dateTime' : undefined

/** Call-site counters, in emission order. */
const callRules: CallRule[] = [
  exactCalls(SUPPORTED_CHOICES, [
    ['queue.push', 'selection.supportAdmissions'],
    ['bucket.dependents.push', 'selection.supportIncidences'],
  ]),
  exactCalls(SELECTION, [
    ['trail.push', 'selection.trailWrites'],
    ['trail.pop', 'selection.trailRestores'],
    ['addIncoming', 'selection.summaryUpdates'],
    ['owners.add', 'selection.assignments'],
    ['owners.delete', 'selection.undo'],
  ]),
  metadataCall,
  exactCalls('src/types/registry.ts', [
    ['module.recognition.test', 'classification.predicateTests'],
  ]),
  intrinsicCall,
  kindMemoMiss,
  exactCalls(FINALIZATION, [['this.untrackedSpecialsToClone.add', 'semantic.activations']]),
  exactCalls(EXECUTION, [['state.checked.add', 'execution.checks']]),
  dateTimeCall,
]

function callKeys(site: Site, node: ts.CallExpression): string[] {
  const called = node.expression.getText(site.file)
  return defined(callRules.map((rule) => rule(site, node, called)))
}

/** Native-boundary metadata is read-only in the supported current owners. */
function metadataRead(site: Site, node: ts.PropertyAccessExpression): string[] {
  const parent = node.parent
  if (
    !site.nativeOwner ||
    !metadata.has(node.name.text) ||
    (ts.isCallExpression(parent) && parent.expression === node)
  )
    return []
  if (
    ts.isBinaryExpression(parent) &&
    parent.left === node &&
    parent.operatorToken.kind === ts.SyntaxKind.EqualsToken
  )
    throw new Error(`Metadata write requires an explicit counter rule: ${site.path}`)
  return [`native.member.${node.name.text}`]
}

/** Graph record literals recognized by the identifier names they define. */
const literalShapes: ReadonlyArray<[key: string, names: string[]]> = [
  ['graph.choiceLiteral', ['identity', 'storage', 'required', 'retained']],
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

/** Execution states built with a computed `revision`. */
function isRevisionLiteral(site: Site, node: ts.ObjectLiteralExpression): boolean {
  return (
    site.path === EXECUTION &&
    node.properties.some(
      (property) =>
        ts.isPropertyAssignment(property) &&
        property.name.getText(site.file) === 'revision' &&
        ts.isBinaryExpression(property.initializer),
    )
  )
}

function objectKeys(site: Site, node: ts.ObjectLiteralExpression): string[] {
  const names = propertyNames(node)
  return defined([
    'allocation.objectLiteral',
    ...literalShapes.map(([key, required]) =>
      required.every((name) => names.has(name)) ? key : undefined,
    ),
    isEdgeLiteral(site.path, names) ? 'graph.edgeLiteral' : undefined,
    isRevisionLiteral(site, node) ? 'execution.revisions' : undefined,
  ])
}

/** Counter keys for an expression, in emission order. */
function counterKeys(site: Site, node: ts.Node): string[] {
  if (ts.isBinaryExpression(node)) return binaryKeys(site, node)
  if (ts.isCallExpression(node)) return callKeys(site, node)
  if (ts.isPropertyAccessExpression(node)) return metadataRead(site, node)
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

/** Each plan that the selection stream yields; delegation to a score tier is not a plan. */
const countPlans: Rewrite = (counter, _node, updated) => {
  if (
    !ts.isYieldExpression(updated) ||
    updated.asteriskToken !== undefined ||
    counter.site.path !== SELECTION ||
    updated.expression === undefined
  )
    return undefined
  return counter.factory.updateYieldExpression(
    updated,
    updated.asteriskToken,
    counter.wrap(updated.expression, ['selection.plans']),
  )
}

/** Every full classification by the `objectKindOf` arrow, per classified value. */
const countObjectKind: Rewrite = (counter, node, updated) => {
  if (
    !ts.isArrowFunction(updated) ||
    !ts.isVariableDeclaration(node.parent) ||
    node.parent.name.getText(counter.site.file) !== 'objectKindOf' ||
    counter.site.path !== 'src/object-kind.ts'
  )
    return undefined
  const f = counter.factory
  const body = ts.isBlock(updated.body)
    ? updated.body.statements
    : [f.createReturnStatement(updated.body)]
  return f.updateArrowFunction(
    updated,
    updated.modifiers,
    updated.typeParameters,
    updated.parameters,
    updated.type,
    updated.equalsGreaterThanToken,
    f.createBlock(
      [
        f.createExpressionStatement(
          counter.tally('classification.full', f.createIdentifier('value')),
        ),
        ...body,
      ],
      true,
    ),
  )
}

/** Function-entry counters by owning file and function name. */
const entryTallies = new Map<string, ReadonlyMap<string, string>>([
  [
    'src/adapters/recognition.ts',
    new Map([
      ['matchesKind', 'classification.expected'],
      ['recognize', 'classification.full'],
    ]),
  ],
  ['src/adapters/vue.ts', new Map([['storageIdentity', 'storage.probes']])],
  ['src/types/shared/property-publication.ts', new Map([['propertySlots', 'shape.indexBuilds']])],
  [
    SELECTION,
    new Map([
      ['compatible', 'selection.compatible'],
      ['selections', 'selection.streams'],
    ]),
  ],
])
/** Entry counters that also count distinct `value` arguments. */
const identityTallies = new Set([
  'classification.expected',
  'classification.full',
  'storage.probes',
])

function entryKey(path: string, name: string | undefined): string | undefined {
  if (name === undefined) return undefined
  if (path === FORCED_GROUPS) return `selection.${name}`
  return entryTallies.get(path)?.get(name)
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

/** Statement-level rewrites; the first that applies wins. */
const rewrites: Rewrite[] = [
  countPlans,
  countObjectKind,
  countFunctionEntry,
  countMethodMemo,
  countArrowMemo,
  countObservation,
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
  const site: Site = {
    file,
    nativeOwner: path.startsWith('src/types/') || nativeOwners.has(path),
    path,
  }
  const sites: Record<string, number> = {}
  // Zero is meaningful only after every checked-store access passes the audit below.
  if (path === EXECUTION) {
    sites['execution.checkedEntriesCopied'] = 0
  }
  const transformed = ts.transform(file, [
    (context) => {
      const counter = createCounter(context, site, sites)
      const visit: ts.Visitor = (node) => {
        const updated = ts.visitEachChild(node, visit, context)
        const copied = countCheckedCopy(counter, node, updated)
        if (copied !== undefined) return copied
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

export const counterSetup = `
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
globalThis.__reconcileCheckedEntries = function* (entries) {
  for (const entry of entries) {
    globalThis.__reconcileCount('execution.checkedEntriesCopied')
    yield entry
  }
}
`
export const counterReset =
  'diagnosticCounts = Object.create(null)\ndiagnosticIdentities = Object.create(null)\n'
export const counterReport = "console.log('RECONCILE_COUNTS ' + JSON.stringify(diagnosticCounts))\n"
