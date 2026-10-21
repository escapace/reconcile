import assert from 'node:assert/strict'
import type { Oracle } from './lean-oracle'
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { ring } from '../src/__tests__/fixtures/ring'
import { immutableDomains } from '../src/__tests__/fixtures/compact-immutable'
import { immutableSelections } from '../src/graph/immutable-selection'
import { supportedChoiceDomains } from '../src/__tests__/fixtures/supported-choices'
import { unsupportedChoices } from '../src/graph/supported-choices'
import { forcedGroupDomains } from '../src/__tests__/fixtures/forced-groups'
import { componentLabels, supportGraph } from '../src/graph/forced-groups'
import { activeDemandDomains } from '../src/__tests__/fixtures/active-demands'
import { forwardDemandDomains } from '../src/__tests__/fixtures/forward-demands'
import { CELL_KIND, Cell, cellType } from '../src/__tests__/fixtures/cell-type'
import { createEngine } from '../src/engine'
import { candidates } from '../src/publication/candidates'
import { capture } from '../src/publication/capture'
import { claimModes, hasClaim, withClaim } from '../src/graph/claims'
import { constructionOrder } from '../src/graph/construction'
import { execute } from '../src/graph/driver'
import { advanceExecution, startExecution } from '../src/graph/execution'
import { chooseSpecial } from '../src/graph/provenance'
import { closeRequirements, RequirementClosure } from '../src/graph/requirements'
import { selections } from '../src/graph/selection'
import { compileImmutable } from '../src/restore-identities'
import type {
  Binding,
  Claims,
  Domains,
  Event,
  Execution,
  ReuseNode,
  SpecialFacts,
  TypeRegistry,
} from '../src/types'
import { builtinModules, builtinTypes } from '../src/types/builtins'
import { OBJECT_KIND, type ObjectLayout } from '../src/types/object'
import { checkPropertyOrderRuntime } from './check-property-order-runtime'
import { checkAtomsRuntime } from './check-atoms-runtime'
import { checkCopyPrototypeRuntime } from './check-copy-prototype-runtime'
import { checkDraftSurfaceRuntime } from './check-draft-surface-runtime'
import { checkDraftClassRuntime } from './check-draft-class-runtime'
import { checkDraftIterationRuntime } from './check-draft-iteration-runtime'
import { checkDraftReadRuntime } from './check-draft-read-runtime'
import { checkDraftMembersRuntime } from './check-draft-members-runtime'
import { checkDraftSetMethodsRuntime } from './check-draft-set-methods-runtime'
import { checkKeyOrderRuntime } from './check-key-order-runtime'
import { checkPropertyConstructRuntime } from './check-property-construct-runtime'
import { checkPropertyThroughSetterRuntime } from './check-property-through-setter-runtime'
import { checkPropertyPlacementRuntime } from './check-property-placement-runtime'
import { checkPropertyWriteRuntime } from './check-property-write-runtime'
import { checkSeededRequirementsRuntime } from './check-seeded-requirements-runtime'
import { checkDeferredOrderRuntime } from './check-deferred-order-runtime'
import { checkFactRenamingRuntime } from './check-fact-renaming-runtime'
import { checkCompactImmutableRuntime } from './check-compact-immutable-runtime'
import { checkSelectionUnwindRuntime } from './check-selection-unwind-runtime'

interface Fixture {
  domains: Domains
  name: string
}
interface Observation {
  name: string
  plans: number[][]
  scores: number[]
}
interface PreferredFixture extends Fixture {
  preferred: number[][]
}
/** One oracle mode: the inputs it receives and the runtime observations it must reproduce. */
interface Comparison {
  inputs: unknown[]
  mode: string
  observations: unknown[]
}
interface DriverFixture extends Fixture {
  ordinary: Array<number | null>
  plans: Array<{ id: number; upper: number }>
  replays: Array<number | null>
  stream: Array<readonly number[]>
}
type Registry = Parameters<typeof candidates>[0]

/** Selects `set` when the fixture variant has `bit`, otherwise `clear`. */
function byBit<T>(variant: number, bit: number, set: T, clear: T): T {
  return (variant & bit) !== 0 ? set : clear
}

/** Relabels native identity/storage labels bijectively to naturals for the finite oracle. */
function numbered(domains: Domains): Domains {
  const labels = new Map<unknown, number>()
  const id = (label: unknown): number => {
    let value = labels.get(label)
    if (value === undefined) labels.set(label, (value = labels.size))
    return value
  }
  return domains.map((domain) =>
    domain.map((choice) => ({
      identity: id(choice.identity),
      required: choice.required.map((edge) => ({ identity: id(edge.identity), node: edge.node })),
      retained: choice.retained,
      storage: id(choice.storage),
    })),
  )
}

function checkedImmutableDomains(types: TypeRegistry, record: ReuseNode): Domains {
  const problem = compileImmutable(types, record)
  const domains = immutableDomains(problem)
  const reference = [...selections(domains)].map((selection) =>
    selection.map((choice, node) => domains[node][choice].retained),
  )
  assert.deepEqual([...immutableSelections(problem)], reference)
  return numbered(domains)
}

/** Native candidate discovery for publishing `next` over `current`, relabeled for the oracle. */
function candidateDomains(types: Registry, next: object, current: object): Domains {
  return numbered(candidates(types, capture(types, next).nodes, current))
}

function family(count: number, name: string, domains: (variant: number) => Domains): Fixture[] {
  return Array.from({ length: count }, (_, variant) => ({
    domains: domains(variant),
    name: `${name}:${variant}`,
  }))
}

/** Every pair of three-slot labelings: each next target may reuse a former occupant or be fresh. */
function aliasFixtures(): Fixture[] {
  const patterns = Array.from({ length: 27 }, (_, n) => [
    n % 3,
    Math.floor(n / 3) % 3,
    Math.floor(n / 9),
  ])
  return patterns.flatMap((before) =>
    patterns.map((after) => ({
      domains: [...new Set(after)].map((target, node) => [
        ...[...new Set(before.filter((_, slot) => after[slot] === target))].map((identity) => ({
          identity,
          required: [],
          retained: true,
          storage: identity,
        })),
        { identity: node + 3, required: [], retained: false, storage: node + 3 },
      ]),
      name: `alias:${before.join(',')}:${after.join(',')}`,
    })),
  )
}

// Native compilation feeds the same finite oracle. These fixtures exercise
// correspondence, frozen parent references, aliases, and distinct node ownership.
function nativeFixture(variant: number): Fixture {
  const before = [{ n: 0 }, { n: 0 }]
  const after = [{ n: 1 }, { n: 1 }]
  const current = { left: before[variant % 2], right: before[Math.floor(variant / 2) % 2] }
  const next = {
    left: after[Math.floor(variant / 4) % 2],
    right: after[Math.floor(variant / 8) % 2],
  }
  if ((variant & 16) !== 0) Object.freeze(current)
  if ((variant & 32) !== 0) Object.freeze(before[0])
  const fixture = {
    domains: candidateDomains(builtinTypes, next, current),
    name: `native:${variant}`,
  }
  assert.equal(before[0].n, 0)
  assert.equal(before[1].n, 0)
  return fixture
}

function specialValues(variant: number) {
  const buffer = new ArrayBuffer(8)
  const date = new Date(variant)
  const typed = new Uint8Array(buffer, variant % 2, 3)
  const view = new DataView((variant & 2) === 0 ? buffer : new ArrayBuffer(8), 1, 4)
  return {
    buffer,
    date,
    n: 0,
    repeated: (variant & 4) === 0 ? date : new Date(variant),
    typed,
    view,
  }
}

// Complete immutable compilation includes settled special identities and explicit
// view-to-buffer dependencies. Scalar/native semantics remain adapter premises.
function immutableSpecialFixture(variant: number): Fixture {
  const current = specialValues(variant)
  const record: ReuseNode<ObjectLayout> = {
    attributes: Object.keys(current).map(() => 7),
    children: Object.entries(current).map(([key, value]) =>
      key === 'n' ? Number((variant & 8) !== 0) : { target: value as object },
    ),
    discoveredBy: undefined,
    keys: Object.keys(current),
    layout: {
      hidden: undefined,
      kind: OBJECT_KIND,
      prototype: (variant & 16) === 0 ? Object.prototype : null,
      slots: undefined,
    },
    leaf: undefined,
    target: current,
  }
  if ((variant & 32) !== 0) Object.freeze(current)
  const fixture = {
    domains: checkedImmutableDomains(builtinTypes, record),
    name: `immutable-special:${variant}`,
  }
  assert.equal(current.n, 0)
  return fixture
}

/** Shared or distinct current and next cells, by bits 1 and 2 of the variant. */
function cellPair(variant: number) {
  const before = new Cell({ n: 0 })
  const after = new Cell({ n: 1 })
  const current = { left: before, right: (variant & 1) === 0 ? before : new Cell({ n: 0 }) }
  const next = { left: after, right: (variant & 2) === 0 ? after : new Cell({ n: 1 }) }
  return { before, current, next }
}

function extensionCandidate(types: Registry, variant: number): Fixture {
  const { before, current, next } = cellPair(variant)
  if ((variant & 4) !== 0) Object.freeze(before)
  if ((variant & 8) !== 0) Object.freeze(current)
  return {
    domains: candidateDomains(types, next, current),
    name: `extension-candidate:${variant}`,
  }
}

function extensionImmutable(types: TypeRegistry, variant: number): Fixture {
  const cell = new Cell(variant % 2)
  const record: ReuseNode<{ readonly kind: typeof CELL_KIND }> = {
    attributes: undefined,
    children: [],
    discoveredBy: undefined,
    keys: ['value'],
    layout: { kind: CELL_KIND },
    leaf: undefined,
    target: cell,
  }
  if ((variant & 2) !== 0) cell.value = cell
  record.children.push((variant & 4) !== 0 ? record : variant % 2)
  if ((variant & 8) !== 0) Object.freeze(cell)
  return {
    domains: checkedImmutableDomains(types, record),
    name: `extension-immutable:${variant}`,
  }
}

// The separately registered native type feeds the existing finite vocabulary.
// Native slot fidelity is a premise; selection is compared over every plan.
function extensionFixtures(): Fixture[] {
  const extension = createEngine({ types: [cellType, ...builtinModules] })
  return Array.from({ length: 16 }, (_, variant) => [
    extensionCandidate(extension.types, variant),
    extensionImmutable(extension.types, variant),
  ]).flat()
}

function sharedFrozenCycle(size: number): Fixture {
  const original = ring(size)
  original.forEach((node) => {
    Object.freeze(node.payload)
    Object.freeze(node)
  })
  const current = { left: original[0], right: original[0] }
  const desired = { left: ring(size)[0], right: ring(size)[0] }
  return {
    domains: candidateDomains(builtinTypes, desired, current),
    name: `shared-frozen-cycle:${size}`,
  }
}

function policyFixtures(): Fixture[] {
  const fixtures = JSON.parse(
    readFileSync('lean/fixtures/policy-fixtures.json', 'utf8'),
  ) as Fixture[]
  return [
    ...fixtures,
    ...family(16, 'forward-demands', forwardDemandDomains),
    ...family(128, 'active-demands', activeDemandDomains),
    ...family(256, 'forced-groups', forcedGroupDomains),
    ...family(256, 'supported-choices', supportedChoiceDomains),
    ...aliasFixtures(),
    ...Array.from({ length: 64 }, (_, variant) => nativeFixture(variant)),
    ...Array.from({ length: 64 }, (_, variant) => immutableSpecialFixture(variant)),
    ...extensionFixtures(),
    ...[2, 3, 4].map((size) => sharedFrozenCycle(size)),
  ]
}

/** Every plan of the ranked stream, by identities, with its retained score. */
function planObservation(
  fixture: Fixture,
  preferFresh?: (rank: number) => ReadonlySet<number>,
): Observation {
  const plans = [...selections(fixture.domains, preferFresh)].map((selection) =>
    selection.map((choice, node) => fixture.domains[node][choice]),
  )
  return {
    name: fixture.name,
    plans: plans.map((plan) => plan.map((choice) => choice.identity as number)),
    scores: plans.map((plan) => plan.reduce((score, choice) => score + Number(choice.retained), 0)),
  }
}

function supportComparison(fixtures: Fixture[]): Comparison {
  return {
    inputs: fixtures,
    mode: 'support',
    observations: fixtures.map((fixture) => {
      const removed = unsupportedChoices(fixture.domains)
      const kept = fixture.domains.flatMap((domain, node) =>
        domain.map((_, choice) => removed?.[node][choice] !== 1),
      )
      return {
        labels: kept.flatMap((supported, id) => (supported ? [id] : [])),
        name: fixture.name,
      }
    }),
  }
}

function groupsComparison(fixtures: Fixture[]): Comparison {
  return {
    inputs: fixtures,
    mode: 'groups',
    observations: fixtures.map((fixture) => ({
      labels: componentLabels(supportGraph(fixture.domains).edges),
      name: fixture.name,
    })),
  }
}

/** Every directed graph on three nodes; edge `source` to `target` is bit `3 * source + target`. */
function graphEdges(mask: number): number[][] {
  return Array.from({ length: 3 }, (_, source) =>
    [0, 1, 2].filter((target) => (mask & (1 << (source * 3 + target))) !== 0),
  )
}

function sccComparison(): Comparison {
  const inputs = Array.from({ length: 512 }, (_, mask) => ({
    edges: graphEdges(mask),
    name: `scc:${mask}`,
  }))
  return {
    inputs,
    mode: 'scc',
    observations: inputs.map((fixture) => ({
      labels: componentLabels(fixture.edges),
      name: fixture.name,
    })),
  }
}

function claimsComparison(): Comparison {
  const inputs = [...Array.from({ length: 512 }, (_, mask) => mask), 2 ** 30, 2 ** 31 - 1].map(
    (mask) => ({
      insertions: [0, 8, 30, 31, 32, 2 ** 32, 0, 31],
      mask,
      name: `claims:${mask}`,
      queries: [...Array.from({ length: 33 }, (_, mode) => mode), 2 ** 32],
    }),
  )
  return {
    inputs,
    mode: 'claims',
    observations: inputs.map((fixture) => {
      let store: Claims = fixture.mask
      const observe = () => ({
        answers: fixture.queries.map((mode) => hasClaim(store, mode)),
        compact: typeof store === 'number',
        modes: [...claimModes(store)].sort((a, b) => a - b),
      })
      const states = [observe()]
      for (const mode of fixture.insertions) {
        store = withClaim(store, mode)
        states.push(observe())
      }
      return { name: fixture.name, states }
    }),
  }
}

function constructionComparison(): Comparison {
  const inputs = Array.from({ length: 4096 }, (_, variant) => ({
    dependencies: graphEdges(variant),
    name: `construction:${variant}`,
    retained: [9, 10, 11].map((bit) => (variant & (1 << bit)) !== 0),
  }))
  return {
    inputs,
    mode: 'construction',
    observations: inputs.map((fixture) => ({
      name: fixture.name,
      order: constructionOrder(fixture.dependencies, fixture.retained) ?? null,
    })),
  }
}

/** Adds rotating fresh-choice preferences per score rank to every fixture. */
function withPreferences(fixtures: Fixture[]): PreferredFixture[] {
  return fixtures.map((fixture, variant) => ({
    ...fixture,
    preferred: Array.from({ length: fixture.domains.length + 1 }, (_, rank) =>
      fixture.domains.flatMap((_, node) => ((node + rank + variant) % 2 === 0 ? [node] : [])),
    ),
  }))
}

function preferenceComparison(mode: string, fixtures: PreferredFixture[]): Comparison {
  return {
    inputs: fixtures,
    mode,
    observations: fixtures.map((fixture) =>
      planObservation(fixture, (rank) => new Set(fixture.preferred[rank])),
    ),
  }
}

function requirementsComparison(): Comparison {
  const inputs = Array.from({ length: 512 }, (_, mask) => ({
    implications: graphEdges(mask),
    name: `closure:${mask}`,
    seeds: [mask % 3],
  }))
  return {
    inputs,
    mode: 'requirements',
    observations: inputs.map((fixture) => ({
      closed: [...closeRequirements(fixture.seeds, fixture.implications)].sort((a, b) => a - b),
      name: fixture.name,
    })),
  }
}

/** Records every prefix of one incremental discovery: implications, seeds and live closure. */
function discoverySteps(variant: number, comparison: Comparison): void {
  const closure = new RequirementClosure()
  const implications: number[][] = [[], [], [], []]
  const seeds: number[] = []
  for (let step = 0; step < 20; step += 1) {
    const from = (variant + step * 3) % 4
    const to = (Math.floor(variant / 4) + step) % 4
    if ((variant + step) % 5 === 0) {
      seeds.push(from)
      closure.require(from)
    } else {
      implications[from].push(to)
      closure.imply(from, to)
    }
    const name = `discovery:${variant}:${step}`
    comparison.inputs.push({
      implications: implications.map((edges) => [...edges]),
      name,
      seeds: [...seeds],
    })
    comparison.observations.push({ closed: [...closure.facts].sort((a, b) => a - b), name })
  }
}

// Compare every prefix of incremental discovery against Lean's full closure.
function discoveryComparison(): Comparison {
  const comparison: Comparison = { inputs: [], mode: 'requirements', observations: [] }
  for (let variant = 0; variant < 96; variant += 1) discoverySteps(variant, comparison)
  return comparison
}

function provenanceComparison(): Comparison {
  const inputs = (['untracked', 'base', 'copy'] as const).flatMap((origin) =>
    Array.from({ length: 16 }, (_, bits) => ({
      facts: {
        currentBacked: (bits & 2) !== 0,
        dependenciesStable: (bits & 1) !== 0,
        equivalent: (bits & 4) !== 0,
        forced: (bits & 8) !== 0,
        origin,
      } satisfies SpecialFacts,
      name: `provenance:${origin}:${bits}`,
    })),
  )
  return {
    inputs,
    mode: 'provenance',
    observations: inputs.map((fixture) => ({
      decision: chooseSpecial(fixture.facts),
      name: fixture.name,
    })),
  }
}

const binding: Binding = {
  choice: 1,
  construction: [],
  exposed: 10,
  fixed: false,
  mode: 0,
  palette: [0, 1, 2],
  storage: 20,
  writer: 30,
}

/** Whether the real rebind guard accepts `exposed` after publication. */
function rebindAccepted(bindings: Binding[], exposed: number, labels: number[]): boolean {
  const checking = advanceExecution(startExecution(7, bindings), {
    id: 7,
    revision: 0,
    tag: 'published',
  })
  const result = advanceExecution(checking, {
    exposed,
    id: 7,
    mode: 1,
    node: 0,
    revision: 0,
    storage: 0,
    tag: 'rebind',
  })
  const accepted = result.phase === 'publishing'
  assert.equal(
    accepted,
    labels.every((label) => label === exposed),
  )
  return accepted
}

function consensusObservation(fixture: { labels: number[]; name: string; queries: number[] }) {
  const bindings: Binding[] = Array.from(
    { length: Math.max(1, fixture.labels.length) },
    (_, node) => ({
      choice: node,
      construction:
        node < fixture.labels.length ? [{ identity: fixture.labels[node], node: 0 }] : [],
      exposed: node,
      fixed: false,
      mode: 0,
      palette: [0, 1],
      storage: node,
      writer: node,
    }),
  )
  const summary = startExecution(7, bindings).incoming[0]
  return {
    answers: fixture.queries.map((exposed) => rebindAccepted(bindings, exposed, fixture.labels)),
    label: summary ?? null,
    name: fixture.name,
    tag: summary === undefined ? 'empty' : summary === null ? 'conflict' : 'one',
  }
}

// Exhaustive equality summaries plus the real rebind guard, including self and peer requirements.
function consensusComparison(): Comparison {
  const inputs = Array.from({ length: 7 }, (_, length) =>
    Array.from({ length: 3 ** length }, (_, code) => ({
      labels: Array.from({ length }, (_, index) => Math.floor(code / 3 ** index) % 3),
      name: `consensus:${length}:${code}`,
      queries: [0, 1, 2, 2 ** 32],
    })),
  ).flat()
  return { inputs, mode: 'consensus', observations: inputs.map(consensusObservation) }
}

function observeExecution(state: Execution) {
  return {
    bindings: state.bindings.map((b) => [b.choice, b.writer, b.exposed, b.storage, b.mode]),
    checked: state.phase === 'checking' ? [...state.checked].sort((a, b) => a - b) : [],
    claims: state.claims.map((claims) => [...claimModes(claims)].sort((a, b) => a - b)),
    id: state.id,
    phase: state.phase,
    revision: state.revision,
  }
}

/** The first rebind varies its node (bit 4), mode (bit 8), storage (bit 16) and id (bit 32). */
function executionTrace(variant: number) {
  const bindings = [
    { ...binding, fixed: (variant & 1) !== 0 },
    {
      ...binding,
      choice: 2,
      construction: byBit(variant, 2, [{ identity: 10, node: 0 }], []),
      exposed: 11,
      storage: 21,
      writer: 31,
    },
  ]
  const events = [
    { tag: 'published' },
    { node: 0, tag: 'checked' },
    {
      exposed: 12,
      id: byBit(variant, 32, 99, 7),
      mode: byBit(variant, 8, 3, 1),
      node: byBit(variant, 4, 5, 0),
      storage: byBit(variant, 16, 99, 20),
      tag: 'rebind',
    },
    { tag: 'finish' },
    { revision: 1, tag: 'published' },
    { node: 0, revision: 1, tag: 'checked' },
    { node: byBit(variant, 64, 4, 1), revision: 1, tag: 'checked' },
    { revision: byBit(variant, 128, 0, 1), tag: 'finish' },
    { exposed: 13, mode: 2, node: 0, revision: 1, storage: 20, tag: 'rebind' },
    { revision: 2, tag: 'published' },
    { exposed: 12, mode: 1, node: 0, revision: 2, storage: 20, tag: 'rebind' },
  ].map((event) => ({ exposed: 0, id: 7, mode: 0, node: 0, revision: 0, storage: 0, ...event }))
  return { bindings, events, id: 7, name: `execution:${variant}` }
}

function executionComparison(): Comparison {
  const traces = Array.from({ length: 256 }, (_, variant) => executionTrace(variant))
  return {
    // The oracle's `Action` decoder keeps the field name `type`; the runtime event
    // discriminant is `tag` so the package build can rename it.
    inputs: traces.map((fixture) => ({
      ...fixture,
      events: fixture.events.map(({ tag, ...event }) => ({ ...event, type: tag })),
    })),
    mode: 'execution',
    observations: traces.map((fixture) => {
      let state = startExecution(fixture.id, fixture.bindings)
      const states = [observeExecution(state)]
      for (const event of fixture.events) {
        state = advanceExecution(state, event as Event)
        states.push(observeExecution(state))
      }
      return { name: fixture.name, states }
    }),
  }
}

/** Deterministic completed reports: a retained count up to `size + 1`, or `null` for failure. */
function reportSource(): (size: number) => number | null {
  let seed = 7139
  return (size) => {
    seed = (Math.imul(seed, 1_664_525) + 1_013_904_223) >>> 0
    const value = (seed >>> 8) % (size + 3)
    return value === size + 2 ? null : value
  }
}

function driverFixture(variant: number, report: (size: number) => number | null): DriverFixture {
  const size = variant % 4
  const domains: Domains = Array.from({ length: size }, (_, node) => [
    { identity: 2 * node, required: [], retained: true, storage: 2 * node },
    { identity: 2 * node + 1, required: [], retained: false, storage: 2 * node + 1 },
  ])
  const stream = [...selections(domains)]
  return {
    domains,
    name: `driver:${variant}`,
    ordinary: stream.map(() => report(size)),
    plans: stream.map((selection, id) => ({
      id,
      upper: selection.reduce(
        (score, choice, node) => score + Number(domains[node][choice].retained),
        0,
      ),
    })),
    replays: stream.map(() => report(size)),
    stream,
  }
}

function driverObservation(fixture: DriverFixture) {
  const indices = new Map(fixture.stream.map((selection, id) => [selection.join(','), id]))
  const visited = new Set<number>()
  const planIds = new Set<number | object>()
  let lastPlan: number | object | undefined
  const trace: Array<{
    candidate: { id: number; upper: number }
    observed: number | null
    replay: boolean
  }> = []
  let reported = 0
  const result = execute(fixture.domains, {
    prepare(selection) {
      const id = indices.get(selection.join(','))!
      const replay = visited.has(id)
      visited.add(id)
      const observed = (replay ? fixture.replays : fixture.ordinary)[id]
      trace.push({ candidate: fixture.plans[id], observed, replay })
      if (observed === null) return undefined
      reported = observed
      return selection.map((choice, node): Binding => ({
        choice,
        construction: [],
        exposed: node,
        fixed: false,
        mode: 0,
        palette: [0],
        storage: node,
        writer: node,
      }))
    },
    publish(state) {
      planIds.add(state.id)
      lastPlan = state.id
      return true
    },
    readback: () => ({ kind: 'match' }),
    retention: () => reported,
  })
  if (result.kind === 'accepted') {
    assert.equal(result.state.id, lastPlan)
    assert.equal(result.state.phase, 'done')
  }
  assert.equal(planIds.size, trace.filter((report) => report.observed !== null).length)
  assert.ok(trace.length <= 2 * fixture.plans.length)
  const answer =
    result.kind === 'rejected'
      ? null
      : {
          candidate:
            fixture.plans[
              indices.get(
                result.state.bindings.map((binding) => binding.choice as number).join(','),
              )!
            ],
          score: reported,
        }
  return { name: fixture.name, result: { answer, trace } }
}

// Drive real prepare/publication/readback transitions while the Lean scheduler
// receives their completed reports. No successful result reuses an old receipt.
function driverComparison(): Comparison {
  const report = reportSource()
  const inputs = Array.from({ length: 512 }, (_, variant) => driverFixture(variant, report))
  return { inputs, mode: 'driver', observations: inputs.map(driverObservation) }
}

/** Every mode after plan selection, in oracle order; each builds its runtime side on demand. */
function modeComparisons(fixtures: Fixture[]): Array<() => Comparison> {
  const preferred = withPreferences(fixtures)
  return [
    () => supportComparison(fixtures),
    () => groupsComparison(fixtures),
    sccComparison,
    claimsComparison,
    constructionComparison,
    () => preferenceComparison('preferred', preferred),
    () =>
      preferenceComparison(
        'forward',
        preferred.filter((fixture) => fixture.name.startsWith('forward-demands:')),
      ),
    requirementsComparison,
    discoveryComparison,
    provenanceComparison,
    consensusComparison,
    executionComparison,
    driverComparison,
  ]
}

async function compareMode(oracle: Oracle, path: string, comparison: Comparison): Promise<void> {
  writeFileSync(path, JSON.stringify(comparison.inputs))
  const reference: unknown = JSON.parse(await oracle('Policy', [path, comparison.mode]))
  assert.deepEqual(comparison.observations, reference)
  console.log(
    `Lean/runtime ${comparison.mode} agreement: ${comparison.inputs.length} fixtures passed.`,
  )
}

async function comparePolicies(oracle: Oracle, path: string, fixtures: Fixture[]): Promise<void> {
  writeFileSync(path, JSON.stringify(fixtures))
  const expected = JSON.parse(await oracle('Policy', [path])) as Observation[]
  assert.deepEqual(
    fixtures.map((fixture) => planObservation(fixture)),
    expected,
  )
  console.log(`Lean/runtime selection agreement: ${fixtures.length} complete plan streams passed.`)
  for (const comparison of modeComparisons(fixtures)) await compareMode(oracle, path, comparison())
}

export async function checkPolicyRuntime(oracle: Oracle): Promise<void> {
  const fixtures = policyFixtures()
  const temporary = mkdtempSync(join(tmpdir(), 'reconcile-policy-'))
  try {
    await comparePolicies(oracle, join(temporary, 'fixtures.json'), fixtures)
  } finally {
    rmSync(temporary, { recursive: true })
  }
  await checkPropertyOrderRuntime(oracle)
  await checkPropertyWriteRuntime(oracle)
  await checkPropertyPlacementRuntime(oracle)
  await checkPropertyConstructRuntime(oracle)
  await checkPropertyThroughSetterRuntime(oracle)
  await checkKeyOrderRuntime(oracle)
  await checkAtomsRuntime(oracle)
  await checkDraftSurfaceRuntime(oracle)
  await checkDraftClassRuntime(oracle)
  await checkDraftIterationRuntime(oracle)
  await checkDraftReadRuntime(oracle)
  await checkDraftMembersRuntime(oracle)
  await checkDraftSetMethodsRuntime(oracle)
  await checkCopyPrototypeRuntime(oracle)
  await checkSeededRequirementsRuntime(oracle)
  await checkDeferredOrderRuntime(oracle)
  await checkFactRenamingRuntime(oracle)
  await checkCompactImmutableRuntime(oracle)
  await checkSelectionUnwindRuntime(oracle)
}
