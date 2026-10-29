// Phase bridge for the `Spec` family: runs `reconcile` from a bundle of the sources that records
// the runtime's discovery and the decision of each pass, and compares them with the reference's
// phases (`SpecOracle.phases`) on the Spec bridge's random graphs: the visit order, the pinning
// alignment, the pinned nodes, each node's candidates in decision order with the requirements of
// their fixed slots, and the decision of every pass. The outcome is the Spec bridge's to compare.
//
// Runtime nodes are next objects in first-visit order. Capture keeps an object already in place as
// an atom edge, so a pinned next node may have no runtime node, or one reached later than the
// reference visits it inside the pinned subtree; order and alignment are compared over the nodes
// that are not pinned, and every pinned node keeps the object it is.
//
// `pnpm check lean spec-phases` runs the bridge alone; `--batch`, `--seeds` and `--dump` narrow it.
import assert from 'node:assert/strict'
import { bundleWithHooks, type Hook } from '../../esbuild'
import type { Oracle } from '../oracle'
import { reproduce, selectBatches, type Selection } from './selection'
import { materialize, materializeClasses, materializeNext, toJs } from '../fixtures/spec-realize'
import {
  GATE_OPTIONS,
  genCase,
  REGRESSION_SEEDS,
  seedRange,
  type Case,
  type Options,
} from '../fixtures/spec-generator'

/** What the reference's phases are, by node id of the next graph and the current graph. */
interface Phases {
  candidates: number[][]
  first: Array<number | null>
  order: number[]
  pinned: boolean[]
  required: Array<Array<Array<[number, number]>>>
  rounds: Array<Array<number | null>>
}

interface RuntimeCandidate {
  identity: object
  required: ReadonlyArray<{ identity: object; node: number }>
}

/** What the instrumented runtime recorded of one call: its discovery and each pass's decision. */
interface Recorded {
  currents: Array<object | undefined>
  domains: RuntimeCandidate[][]
  passes: Array<Array<object | undefined>>
  pinned: Array<object | undefined>
  sources: object[]
}

interface Recorder {
  decided: (kept: ReadonlyArray<object | undefined>) => void
  discovered: (
    graph: {
      currents: ReadonlyArray<object | undefined>
      nodes: ReadonlyArray<{ pinned?: object; source?: object }>
    },
    domains: readonly RuntimeCandidate[][],
  ) => void
}

const RECORDER = '__reconcilePhases'

/** The statements of `publishGraph` after which the recorder runs, and what it records there. */
const HOOKS: readonly Hook[] = [
  [
    'const domains = candidates(types, records, root, graph, note)\n',
    `globalThis.${RECORDER}?.discovered(graph, domains)\n`,
  ],
  [
    'const kept = decide(records, domains, graph.reads, run.passes)\n',
    `globalThis.${RECORDER}?.decided(kept)\n`,
  ],
]

export type Library = typeof import('../../../src/index')

let bundled: Promise<Library> | undefined

/** The sources bundled with the recorder calls after each hook's statement, loaded once per
 * process; the phase gate and the enumeration share it. */
export const instrumented = async (): Promise<Library> =>
  await (bundled ??= bundleWithHooks(
    "export * from './src/index'",
    /publication-engine\.ts$/,
    HOOKS,
  ) as Promise<Library>)

/** Runs `operation` with the recorder installed; the recording, or undefined when the call
 * published nothing. */
function recording(operation: () => void): Recorded | undefined {
  let recorded: Recorded | undefined
  const recorder: Recorder = {
    decided: (kept) => recorded!.passes.push([...kept]),
    discovered: (graph, domains) => {
      recorded = {
        currents: [...graph.currents],
        domains: domains.map((domain) =>
          domain.map(({ identity, required }) => ({ identity, required: [...required] })),
        ),
        passes: [],
        pinned: graph.nodes.map((node) => node.pinned),
        sources: graph.nodes.map((node) => node.source!),
      }
    },
  }
  Reflect.set(globalThis, RECORDER, recorder)
  try {
    operation()
  } finally {
    Reflect.deleteProperty(globalThis, RECORDER)
  }
  return recorded
}

const show = (value: unknown): string => JSON.stringify(value)

/** One case under comparison: the reference's phases, the runtime's recording, the next node of
 * each runtime node, and the differences found so far. */
interface Comparison {
  readonly c: Case
  readonly differences: string[]
  readonly got: Recorded
  readonly nodes: readonly number[]
  readonly want: Phases
  readonly idOf: (object: object | undefined) => number | null
}

/** The current object a pinned next node keeps, which is the node itself; null for another node. */
const pinnedTo = (cx: Comparison, nextNode: number): number | null =>
  cx.want.pinned[nextNode] ? cx.c.same[nextNode] : null

function compareOrder(cx: Comparison): void {
  const order = cx.nodes.filter((nextNode) => !cx.want.pinned[nextNode])
  const wanted = cx.want.order.filter((nextNode) => !cx.want.pinned[nextNode])
  if (show(order) !== show(wanted))
    cx.differences.push(`order ${show(order)}, reference ${show(wanted)}`)
}

/** Compares the requirements of runtime node `k`'s candidates, which match the reference's. */
function compareRequired(cx: Comparison, nextNode: number, k: number): void {
  cx.got.domains[k].forEach((candidate, at) => {
    const required = candidate.required.map(({ identity, node }) => [
      cx.nodes[node],
      cx.idOf(identity),
    ])
    // A requirement at a node kept as an atom edge holds already: it is the object there.
    const wanted = cx.want.required[nextNode][at].filter(([d]) => cx.nodes.includes(d))
    if (show(required) !== show(wanted))
      cx.differences.push(
        `node ${nextNode} candidate ${cx.idOf(candidate.identity)} requires ${show(required)}, reference ${show(wanted)}`,
      )
  })
}

/** Compares the alignment and the candidates of runtime node `k`, which is `nextNode`. */
function compareUnpinned(cx: Comparison, nextNode: number, k: number): void {
  const aligned = cx.idOf(cx.got.currents[k])
  if (aligned !== cx.want.first[nextNode])
    cx.differences.push(`node ${nextNode} aligned ${aligned}, reference ${cx.want.first[nextNode]}`)
  const identities = show(cx.got.domains[k].map((candidate) => cx.idOf(candidate.identity)))
  if (identities === show(cx.want.candidates[nextNode])) compareRequired(cx, nextNode, k)
  else
    cx.differences.push(
      `node ${nextNode} candidates ${identities}, reference ${show(cx.want.candidates[nextNode])}`,
    )
}

/** Compares runtime node `k`, which is `nextNode`: its pinning, then, unless pinned, its
 * alignment and candidates. */
function compareNode(cx: Comparison, nextNode: number, k: number): void {
  const pinned = cx.idOf(cx.got.pinned[k])
  if (pinned !== pinnedTo(cx, nextNode))
    cx.differences.push(`node ${nextNode} pinned to ${pinned}, reference ${pinnedTo(cx, nextNode)}`)
  if (!cx.want.pinned[nextNode]) compareUnpinned(cx, nextNode, k)
}

/** Compares the decision of each pass; a pinned node without a runtime node keeps the object it
 * is. */
function compareRounds(cx: Comparison): void {
  const { got, want } = cx
  if (got.passes.length !== want.rounds.length)
    cx.differences.push(`passes ${got.passes.length}, reference ${want.rounds.length}`)
  got.passes.forEach((kept, pass) => {
    const decided = new Map(cx.nodes.map((nextNode, k) => [nextNode, cx.idOf(kept[k])]))
    want.rounds[pass]?.forEach((x, nextNode) => {
      const actual = decided.has(nextNode) ? decided.get(nextNode) : pinnedTo(cx, nextNode)
      if (actual !== x)
        cx.differences.push(`pass ${pass} node ${nextNode} keeps ${actual}, reference ${x}`)
    })
  })
}

/** The differences between what the runtime recorded and the reference's phases. */
function comparePhases(
  c: Case,
  want: Phases,
  got: Recorded,
  current: readonly object[],
  next: readonly object[],
): string[] {
  const currentIds = new Map(current.map((object, index) => [object, index]))
  const nextIds = new Map(next.map((object, index) => [object, index]))
  const nodes = got.sources.map((source) => nextIds.get(source) ?? -1)
  if (nodes.includes(-1)) return [`runtime node outside next: ${show(nodes)}`]
  const idOf = (object: object | undefined): number | null =>
    object === undefined ? null : (currentIds.get(object) ?? -1)
  const cx: Comparison = { c, differences: [], got, idOf, nodes, want }
  compareOrder(cx)
  nodes.forEach((nextNode, k) => compareNode(cx, nextNode, k))
  compareRounds(cx)
  return cx.differences
}

export interface PhaseReport {
  detail: string
  seed: number
}

/** Runs `reconcile` on the instrumented runtime: what it recorded, or the error it threw that is
 * not a reconcile error. */
function run(library: Library, current: unknown, next: unknown): Error | Recorded | undefined {
  let failure: Error | undefined
  const got = recording(() => {
    try {
      library.reconcile(current, next)
    } catch (error) {
      if (!library.isReconcileError(error)) failure = new Error(String(error))
    }
  })
  return failure ?? got
}

/** Whether a call that published nothing agrees with the reference: the runtime publishes
 * nothing when the roots are one object, and the reference decides nothing for a primitive root. */
const unpublished = (want: Phases, current: unknown, next: unknown): boolean =>
  Object.is(current, next) || want.rounds.length === 0

/** Runs one case on the instrumented runtime and compares its phases with the reference's. */
function checkCase(library: Library, seed: number, c: Case, want: Phases): PhaseReport[] {
  const classes = materializeClasses(c.classes, new Map())
  const current = materialize(c.cur, new Map(), undefined, undefined, classes)
  const next = materializeNext(c, current, classes)
  const roots = [toJs(c.cur.root, current), toJs(c.next.root, next)] as const
  const got = run(library, ...roots)
  if (got instanceof Error) return [{ detail: `runtime threw ${got.message}`, seed }]
  if (got === undefined)
    return unpublished(want, ...roots) ? [] : [{ detail: 'runtime published nothing', seed }]
  return comparePhases(c, want, got, current, next).map((detail) => ({ detail, seed }))
}

const request = (c: Case): object => ({
  classes: c.classes,
  cur: c.cur,
  next: c.next,
  op: 'reconcile-phases',
  same: c.same,
})

/** Generates the cases of `seeds`, asks the oracle once for their phases and compares. */
async function checkPhases(
  library: Library,
  oracle: Oracle,
  seeds: readonly number[],
  options: Options,
): Promise<{ cases: number; passes: number; reports: PhaseReport[] }> {
  const cases = seeds.map((seed) => genCase(seed, options))
  return { cases: cases.length, ...(await checkPhaseCases(library, oracle, cases, seeds)) }
}

/** Asks the oracle once for the phases of `cases` and compares each, reported under its id, by
 * default its index. */
export async function checkPhaseCases(
  library: Library,
  oracle: Oracle,
  cases: readonly Case[],
  ids: readonly number[] = cases.map((_, index) => index),
): Promise<{ passes: number; reports: PhaseReport[] }> {
  const input = JSON.stringify(cases.map(request))
  const output = (await oracle('Spec', { input, maxBuffer: 256 * 1024 * 1024 })).trim()
  const phases = JSON.parse(output) as Phases[]
  assert.equal(phases.length, cases.length)
  const reports = cases.flatMap((c, index) => checkCase(library, ids[index], c, phases[index]))
  const passes = phases.reduce((sum, p) => sum + p.rounds.length, 0)
  return { passes, reports }
}

/** The gate's batches, by the name `pnpm check lean spec-phases --batch` takes: the default
 * cases, hazard-rich ones and buffers and views beside the other kinds. */
const PHASE_BATCHES: ReadonlyArray<{
  readonly count: number
  readonly name: string
  readonly options: Options
  readonly regressions: readonly number[]
}> = [
  { count: 1500, name: 'plain', options: GATE_OPTIONS, regressions: REGRESSION_SEEDS.plain },
  {
    count: 3000,
    name: 'hazards',
    options: { ...GATE_OPTIONS, hazards: true },
    regressions: REGRESSION_SEEDS.hazards,
  },
  { count: 1500, name: 'binary', options: { ...GATE_OPTIONS, binary: true }, regressions: [] },
]

/** The batches, by the name `pnpm check lean spec-phases --batch` takes. */
export const phaseBatchNames = (): string[] => PHASE_BATCHES.map((batch) => batch.name)

/** Shows one case and the reference's phases. */
async function dump(oracle: Oracle, seed: number, options: Options): Promise<void> {
  const c = genCase(seed, options)
  console.log(`--- seed ${seed}\ncur  ${show(c.cur)}\nnext ${show(c.next)}\nsame ${show(c.same)}`)
  const input = JSON.stringify([request(c)])
  console.log(`reference ${(await oracle('Spec', { input })).trim()}`)
}

/** The gate's batches, or those `selection` names, each over its own seeds or the selected ones:
 * every phase difference fails. A dump shows each seed's case and differences instead. */
export async function checkSpecPhasesGate(
  oracle: Oracle,
  selection: Selection = {},
): Promise<void> {
  const library = await instrumented()
  const summaries: string[] = []
  for (const batch of selectBatches(PHASE_BATCHES, selection)) {
    const seeds = selection.seeds ?? [...seedRange(1, batch.count), ...batch.regressions]
    if (selection.dump === true) for (const seed of seeds) await dump(oracle, seed, batch.options)
    const { cases, passes, reports } = await checkPhases(library, oracle, seeds, batch.options)
    for (const r of reports.slice(0, 5)) console.log(`seed ${r.seed}: ${r.detail}`)
    if (reports.length > 0 && selection.dump !== true)
      assert.fail(
        `Spec phases (${batch.name}): ${reports.length} differences. ` +
          `Show one: ${reproduce('spec-phases', batch.name, reports[0].seed)}`,
      )
    summaries.push(`${cases} ${batch.name} cases (${passes} passes)`)
  }
  if (selection.dump !== true) console.log(`Spec phases: ${summaries.join(', ')} agree`)
}
