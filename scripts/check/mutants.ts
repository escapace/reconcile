// The mutation audit: checks that the Spec bridges and the collection-writes bridge detect runtime
// defects. It copies the working tree, runs every bridge it needs on the unmutated copy, which
// must agree, then applies one deliberate defect, a mutant, at a time to the copy's runtime
// sources and runs the reconcile bridge, or the phase or collection-writes bridge where a mutant
// names it, expecting it to fail. A mutant that survives names a case the generator does not
// produce or a difference the comparison does not see; a mutant expected to survive names the gap
// it stands for, and a verdict that differs from the expectation, in either direction, fails the
// audit. The working tree itself is never written.
//
//   pnpm check mutants [name...] [--seeds N]
import assert from 'node:assert/strict'
import { spawn } from 'node:child_process'
import {
  chmodSync,
  copyFileSync,
  existsSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  rmSync,
  statSync,
  symlinkSync,
  writeFileSync,
} from 'node:fs'
import { tmpdir } from 'node:os'
import path from 'node:path'
import { parseArgs } from 'node:util'
import { treeFiles } from '../framework/fingerprint'
import { ROOT } from '../framework/paths'

interface Mutant {
  readonly file: string
  /** The exact source text, present once, that the defect replaces. */
  readonly find: string
  readonly name: string
  readonly replace: string
  /** The bridge that must see the defect: the outcome bridge unless it names the phase bridge,
   * for a defect only the runtime's discovery or decisions show, or the collection-writes bridge,
   * for one only the writes to a kept `Map` or `Set` show. */
  readonly bridge?: 'collections' | 'phases'
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
    bridge: 'phases',
    file: 'src/publication/capture.ts',
    find: 'isObject(occupant) && occupant !== this.currents[known.node]',
    name: 'alias-offer-ignored',
    replace: 'false',
  },
  {
    bridge: 'phases',
    file: 'src/publication/capture.ts',
    find: '      this.offersOther = true\n      return this.visit(child, kind)\n',
    name: 'entry-offer-ignored',
    replace: '      return this.visit(child, kind)\n',
  },
  {
    file: 'src/publication/capture.ts',
    find: '      for (let next = stack.pop(); next !== undefined; next = stack.pop()) {\n',
    name: 'keep-walk-breadth-first',
    replace: '      for (let next = stack.shift(); next !== undefined; next = stack.shift()) {\n',
  },
  {
    file: 'src/types/object.ts',
    find: '      edge(Reflect.get(value, names[index]) as unknown, names[index])\n',
    name: 'next-property-read-twice',
    replace:
      '      edge((Reflect.get(value, names[index]), Reflect.get(value, names[index])) as unknown, names[index])\n',
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
    file: ENGINE,
    find: '  if (target !== node.source) return !graph.references.has(target)\n',
    name: 'next-held-elsewhere-kept',
    replace: '  if (target !== node.source) return true\n',
  },
  {
    file: ENGINE,
    find: '    if (isNode(edge) && kept[edge.node] !== records[edge.node].source) return false\n',
    name: 'untouched-child-unchecked',
    replace: '',
  },
  {
    file: ENGINE,
    find: '=> target === node.source\n',
    name: 'untouched-published',
    replace: '=> node.pinned !== undefined\n',
  },
  {
    file: 'src/publication/candidates.ts',
    find: '      candidate === node.source &&\n      policy.aligned === alignedProperties\n',
    name: 'own-node-walk-read',
    replace: '      false &&\n      policy.aligned === alignedProperties\n',
  },
  {
    file: 'src/publication/capture.ts',
    find: '      aligned === (this.nodes[parent] as BuildingNode).source\n',
    name: 'own-node-occupant-read',
    replace: '      false\n',
  },
  {
    file: 'src/publication/candidates.ts',
    find: '          records[first].source === candidate ? undefined : readsAt(alignment, candidate, first)\n',
    name: 'own-node-walk-shared',
    replace: '          readsAt(alignment, candidate, first)\n',
  },
  {
    file: 'src/publication/capture.ts',
    find: '      const reads = node.source === object ? undefined : this.occupants[first]\n',
    name: 'own-node-occupants-shared',
    replace: '      const reads = this.occupants[first]\n',
  },
  {
    file: 'src/types/shared/property-publication.ts',
    find: '  return required ?? EMPTY_FACTS\n',
    name: 'own-node-pins-dropped',
    replace: '  return EMPTY_FACTS\n',
  },
  {
    file: 'src/types/shared/property-publication.ts',
    find: '    if (descriptor !== undefined && !recreatable(descriptor) && unwritable(descriptor))\n',
    name: 'own-node-writable-fixed',
    replace: '    if (descriptor !== undefined && !recreatable(descriptor))\n',
  },
  {
    file: 'src/types/shared/property-publication.ts',
    find: '    if (descriptor !== undefined && !recreatable(descriptor) && unwritable(descriptor))\n',
    name: 'own-node-getter-unpinned',
    replace:
      '    if (descriptor !== undefined && !recreatable(descriptor) && isDataDescriptor(descriptor) && unwritable(descriptor))\n',
  },
  {
    bridge: 'collections',
    file: 'src/types/shared/collection.ts',
    find: '        if (position < wanted && sameKey(key, resolve(edges[position * width]))) {',
    name: 'retain-prefix-by-index',
    replace:
      '        if (position < wanted && index === position && sameKey(key, resolve(edges[position * width]))) {',
  },
]

type Verdict = 'hung' | 'killed' | 'survived'

/** Each bridge's command, the text its output holds when it saw nothing, whether it takes the
 * seed count, and its runs: the outcome bridge plain, through recording proxies and on
 * hazard-rich cases; the phase bridge with buffers and views beside the other kinds, plain and on
 * hazard-rich cases; the collection-writes bridge once, over its fixed corpus. */
const BRIDGES = {
  collections: {
    agreed: 'Collection-writes Lean/native bridge:',
    command: ['scripts/check-collection-writes-runtime.ts'],
    runs: [[]],
    seeded: false,
  },
  outcome: {
    agreed: 'reports 0;',
    command: ['scripts/lean-spec-bridge.ts', '--op', 'reconcile'],
    runs: [[], ['--writes'], ['--writes', '--hazards']],
    seeded: true,
  },
  phases: {
    agreed: 'differences 0',
    command: ['scripts/lean-spec-phases.ts'],
    runs: [['--binary'], [], ['--hazards']],
    seeded: true,
  },
} as const

type Bridge = (typeof BRIDGES)[keyof typeof BRIDGES]

/** The seed count for a bridge that takes one. */
const seedArguments = (bridge: Bridge, seeds: number): string[] =>
  bridge.seeded ? ['--seeds', String(seeds)] : []

/** The oracle every bridge runs, built by the round's first step. */
const ORACLE = path.join('.lake', 'build', 'bin', 'reconcile-oracle')

/**
 * A copy of the working tree, tracked and untracked files alike, in which mutants are applied:
 * the installed dependencies and the built oracle are linked, not copied.
 */
function copyTree(): string {
  const oracle = path.join(ROOT, ORACLE)
  if (!existsSync(oracle)) {
    console.error(`The oracle ${oracle} is missing; the round builds it first.`)
    process.exit(3)
  }
  const copy = mkdtempSync(path.join(tmpdir(), 'reconcile-mutants-'))
  for (const file of treeFiles()) {
    const from = path.join(ROOT, file)
    if (!existsSync(from)) continue
    const to = path.join(copy, file)
    mkdirSync(path.dirname(to), { recursive: true })
    copyFileSync(from, to)
    chmodSync(to, statSync(from).mode)
  }
  symlinkSync(path.join(ROOT, 'node_modules'), path.join(copy, 'node_modules'))
  mkdirSync(path.join(copy, path.dirname(ORACLE)), { recursive: true })
  symlinkSync(oracle, path.join(copy, ORACLE))
  return copy
}

/** One bridge run in the copy. It saw nothing when it finished with the bridge's report of no
 * difference; a mutant that throws inside the runtime is caught as well, since the bridge reports
 * errors. A run takes some seconds; one that loops is cut off well inside the round. The run
 * stays in the round's process group, so that the round can stop it. */
async function runBridge(
  copy: string,
  bridge: Bridge,
  seeds: number,
  flags: readonly string[],
): Promise<Verdict> {
  return await new Promise((resolve) => {
    const child = spawn(
      process.execPath,
      ['--import', 'tsx', ...bridge.command, ...seedArguments(bridge, seeds), ...flags],
      { cwd: copy, stdio: ['ignore', 'pipe', 'pipe'] },
    )
    let output = ''
    let hung = false
    const collect = (chunk: string): void => {
      output += chunk
    }
    child.stdout.setEncoding('utf8').on('data', collect)
    child.stderr.setEncoding('utf8').on('data', collect)
    const timer = setTimeout(() => {
      hung = true
      child.kill('SIGKILL')
    }, 30_000)
    child.on('error', () => {
      clearTimeout(timer)
      resolve('hung')
    })
    child.on('close', (status) => {
      clearTimeout(timer)
      if (hung) resolve('hung')
      else resolve(status === 0 && output.includes(bridge.agreed) ? 'survived' : 'killed')
    })
  })
}

/** The bridge's runs, all at once: the verdict is the first run, in order, that did not end or
 * saw a difference, as running them one after another until one does would find. */
async function runAll(copy: string, bridge: Bridge, seeds: number): Promise<Verdict> {
  const verdicts = await Promise.all(
    bridge.runs.map(async (flags) => await runBridge(copy, bridge, seeds, flags)),
  )
  return verdicts.find((verdict) => verdict !== 'survived') ?? 'survived'
}

async function audit(copy: string, mutant: Mutant, seeds: number): Promise<Verdict> {
  const file = path.join(copy, mutant.file)
  const original = readFileSync(file, 'utf8')
  assert.equal(original.split(mutant.find).length, 2, `${mutant.name}: find text not present once`)
  writeFileSync(file, original.replace(mutant.find, mutant.replace))
  try {
    return await runAll(copy, BRIDGES[mutant.bridge ?? 'outcome'], seeds)
  } finally {
    writeFileSync(file, original)
  }
}

const { positionals, values } = parseArgs({
  allowPositionals: true,
  options: { seeds: { default: '1500', type: 'string' } },
})
const unknown = positionals.filter((name) => !MUTANTS.some((mutant) => mutant.name === name))
if (unknown.length > 0) {
  console.error(`Unknown mutants: ${unknown.join(', ')}.`)
  process.exit(2)
}
const selected = MUTANTS.filter((m) => positionals.length === 0 || positionals.includes(m.name))
const seeds = Number(values.seeds)
const copy = copyTree()
// The round stops this process with SIGTERM on timeout or interruption; the copy goes with it.
process.once('SIGTERM', () => {
  rmSync(copy, { force: true, recursive: true })
  process.exit(143)
})
let surprises = 0
try {
  // An unmutated run that does not agree means the copy, not a mutant, is broken: every mutant
  // would then read as killed.
  const started = Date.now()
  const needed = [...new Set(selected.map((mutant) => mutant.bridge ?? 'outcome'))]
  const controls = await Promise.all(
    needed.map(async (name) => [name, await runAll(copy, BRIDGES[name], seeds)] as const),
  )
  const broken = controls.filter(([, verdict]) => verdict !== 'survived')
  if (broken.length > 0) {
    console.error(
      `The unmutated copy does not agree (${broken.map(([name, verdict]) => `${name}: ${verdict}`).join(', ')}): ` +
        'the audit cannot judge any mutant.',
    )
    process.exit(1)
  }
  const seconds = Math.round((Date.now() - started) / 1000)
  console.log(`control: ${needed.join(', ')} agree on the unmutated copy in ${seconds} s`)
  for (const mutant of selected) {
    const begun = Date.now()
    const verdict = await audit(copy, mutant, seeds)
    const expected = (verdict === 'survived') === (mutant.survives !== undefined)
    if (!expected) surprises += 1
    const note = mutant.survives === undefined ? '' : ` (expected to survive: ${mutant.survives})`
    const elapsed = Math.round((Date.now() - begun) / 1000)
    console.log(
      `${expected ? verdict : `UNEXPECTED ${verdict}`} ${mutant.name} in ${elapsed} s${note}`,
    )
  }
} finally {
  rmSync(copy, { force: true, recursive: true })
}
console.log(`${selected.length - surprises} of ${selected.length} verdicts as expected`)
if (surprises > 0) process.exitCode = 1
