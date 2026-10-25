// Sensitivity audit of the Spec bridges: applies one deliberate defect at a time to the runtime
// sources, runs the strict reconcile bridge, or the phase bridge where a mutant names it, in a
// child process and expects it to fail. A mutant
// that survives names a case the generator does not produce or a difference the comparison does
// not see; a mutant expected to survive names the gap it stands for, and a verdict that differs
// from the expectation, in either direction, fails the audit. The sources are restored after every
// mutant, whatever happens.
//
//   pnpm exec tsx scripts/spec-mutants.ts [--seeds N] [--only NAME]
import assert from 'node:assert/strict'
import { spawnSync, type SpawnSyncReturns } from 'node:child_process'
import { readFileSync, writeFileSync } from 'node:fs'
import { parseArgs } from 'node:util'

interface Mutant {
  /** The bridge that must see the defect: the outcome bridge unless it names the phase bridge,
   * for a defect only the runtime's discovery or decisions show. */
  readonly bridge?: 'phases'
  /** The exact source text, present once, that the defect replaces. */
  readonly file: string
  readonly find: string
  readonly name: string
  readonly replace: string
  /** Why the bridge is expected not to see this mutant: the gap it stands for. */
  readonly survives?: string
}

const ENGINE = 'src/publication/publication-engine.ts'
const MUTANTS: readonly Mutant[] = [
  {
    file: ENGINE,
    find: '  for (let at = 0; at < domain.length; at += 1) {',
    name: 'candidate-order-reversed',
    replace: '  for (let at = domain.length - 1; at >= 0; at -= 1) {',
  },
  {
    file: ENGINE,
    find: '  if (published === WRITE_FREE && run.passes === undefined) return undefined\n',
    name: 'readback-skipped',
    replace: '  return published === WRITE_FREE ? undefined : published\n',
  },
  {
    file: ENGINE,
    find: '  state.passes?.forbidden.has(x) !== true && !reservedElsewhere(state, c, x)',
    name: 'forbidden-ignored',
    replace: '  !reservedElsewhere(state, c, x)',
  },
  {
    file: ENGINE,
    find: '  state.used?.has(x) === true && state.passes?.written.get(x) !== c',
    name: 'reservation-ignored',
    replace: '  false && state.used?.has(x) === true && state.passes?.written.get(x) !== c',
  },
  {
    file: 'src/types/shared/property-publication.ts',
    find: '    this.cursor += 1\n    this.stale = true\n    return true\n',
    name: 'every-key-moved',
    replace: '    this.cursor += 1\n    this.stale = true\n    return false\n',
  },
  {
    file: ENGINE,
    find: '  for (let index = 0; index < blocked.length; index += 1) state.forbidden.add(blocked[index])',
    name: 'blocked-not-forbidden',
    replace: '  for (let index = 0; index < 0; index += 1) state.forbidden.add(blocked[index])',
  },
  {
    file: 'src/publication/candidates.ts',
    find: '  promoteDemanded(domains)\n',
    name: 'promotion-skipped',
    replace: '\n',
  },
  {
    bridge: 'phases',
    file: 'src/publication/candidates.ts',
    find: 'pinsAnother(records, required)',
    name: 'pinned-demand-admitted',
    replace: 'pinsAnother(records, [])',
  },
  {
    file: 'src/publication/capture.ts',
    find: '    if (key !== undefined) node.keys.push(key)\n    const child = this.adopt(reference.node, value, key, construction, knownKind)\n',
    name: 'key-pushed-after-adopt',
    replace:
      '    const child = this.adopt(reference.node, value, key, construction, knownKind)\n    if (key !== undefined) node.keys.push(key)\n',
  },
  {
    file: 'src/types/shared/properties.ts',
    find: '  hasOwn(current, key) ? Reflect.get(current, key) : undefined',
    name: 'own-value-through-prototype',
    replace: '  Reflect.get(current, key)',
  },
  {
    file: 'src/types/shared/property-publication.ts',
    find: '    if (Object.is(read, value) && present) return UNCHANGED\n',
    name: 'unchanged-without-presence',
    replace: '    if (Object.is(read, value)) return UNCHANGED\n',
  },
  {
    file: 'src/types/object.ts',
    find: '    if (keys[index] !== expected[index]) return false\n',
    name: 'key-order-unchecked',
    replace: '    if (keys[index] !== expected[index]) continue\n',
    survives: 'only a trap can reorder keys between capture and readback; proxies are not modelled',
  },
  {
    file: 'src/types/shared/collection.ts',
    find: '        if (position < wanted && sameKey(key, resolve(edges[position * width]))) {',
    name: 'retain-prefix-by-index',
    replace:
      '        if (position < wanted && index === position && sameKey(key, resolve(edges[position * width]))) {',
    survives:
      'an entry moved inside a Map or Set is deleted and re-added with the built-in methods, which the result does not show',
  },
]

type Verdict = 'hung' | 'killed' | 'survived'

/** Each bridge's command, the text its output holds when it saw nothing, and its runs: the
 * outcome bridge plain, through recording proxies and on hazard-rich cases; the phase bridge
 * with buffers and views beside the other kinds, plain and on hazard-rich cases. */
const BRIDGES = {
  outcome: {
    agreed: 'reports 0;',
    command: ['scripts/lean-spec-bridge.ts', '--op', 'reconcile', '--strict'],
    runs: [[], ['--writes'], ['--writes', '--hazards']],
  },
  phases: {
    agreed: 'differences 0',
    command: ['scripts/lean-spec-phases.ts'],
    runs: [['--binary'], [], ['--hazards']],
  },
} as const

type Bridge = (typeof BRIDGES)[keyof typeof BRIDGES]

function runBridge(bridge: Bridge, seeds: number, flags: readonly string[]): Verdict {
  const result = spawnSync(
    'pnpm',
    ['exec', 'tsx', ...bridge.command, '--seeds', String(seeds), ...flags],
    // A bridge run takes a few seconds; a mutant that loops is cut off well inside the round.
    { encoding: 'utf8', timeout: 30_000 },
  )
  return verdictOf(bridge, result)
}

type Run = SpawnSyncReturns<string>

/** Whether the bridge finished and saw nothing; a mutant that throws inside the runtime is
 * caught as well, since the bridge reports errors. */
const agreed = (bridge: Bridge, result: Run): boolean =>
  result.status === 0 && `${result.stdout}\n${result.stderr}`.includes(bridge.agreed)

function verdictOf(bridge: Bridge, result: Run): Verdict {
  if (result.error !== undefined || result.signal !== null) return 'hung'
  return agreed(bridge, result) ? 'survived' : 'killed'
}

/** The bridge's runs in order, each as long as the previous run saw nothing. */
function runAll(bridge: Bridge, seeds: number): Verdict {
  let verdict: Verdict = 'survived'
  for (const flags of bridge.runs) {
    verdict = runBridge(bridge, seeds, flags)
    if (verdict !== 'survived') break
  }
  return verdict
}

function audit(mutant: Mutant, seeds: number): Verdict {
  const original = readFileSync(mutant.file, 'utf8')
  assert.equal(original.split(mutant.find).length, 2, `${mutant.name}: find text not present once`)
  writeFileSync(mutant.file, original.replace(mutant.find, mutant.replace))
  try {
    return runAll(BRIDGES[mutant.bridge ?? 'outcome'], seeds)
  } finally {
    writeFileSync(mutant.file, original)
  }
}

const { values } = parseArgs({
  options: { only: { type: 'string' }, seeds: { default: '1500', type: 'string' } },
})
const selected = MUTANTS.filter((m) => values.only === undefined || m.name === values.only)
assert.ok(selected.length > 0, 'no mutant selected')
let surprises = 0
for (const mutant of selected) {
  const started = Date.now()
  const verdict = audit(mutant, Number(values.seeds))
  const expected = (verdict === 'survived') === (mutant.survives !== undefined)
  if (!expected) surprises += 1
  const note = mutant.survives === undefined ? '' : ` (expected to survive: ${mutant.survives})`
  const seconds = Math.round((Date.now() - started) / 1000)
  console.log(
    `${expected ? verdict : `UNEXPECTED ${verdict}`} ${mutant.name} in ${seconds} s${note}`,
  )
}
console.log(`${selected.length - surprises} of ${selected.length} verdicts as expected`)
if (surprises > 0) process.exitCode = 1
