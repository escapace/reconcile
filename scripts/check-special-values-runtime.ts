// Runs `chooseSpecial` on every combination of facts, and `produce` on every scenario of
// `Produce.SpecialValues` the oracle generates, against Lean's decision and resolution.
import assert from 'node:assert/strict'
import { chooseSpecial } from '../src/graph/provenance'
import type { SpecialFacts } from '../src/types'
import { bundleWithHooks, type Hook } from './esbuild'
import { integerIn, jsonObject, oracleCorpus, type Oracle } from './lean-oracle'

type Library = typeof import('../src/index')
type Recorder = (facts: SpecialFacts) => void

const RECORDER = '__reconcileSpecialFacts'

/** Records the facts of every decision at the start of `chooseSpecial`. */
const HOOKS: readonly Hook[] = [
  [
    'export function chooseSpecial(facts: SpecialFacts): SpecialDecision {\n',
    `globalThis.${RECORDER}?.(facts)\n`,
  ],
]

interface ValueRow {
  readonly dep: number | null
  readonly edit: boolean
  readonly native: string
  readonly read: boolean
  readonly touch: boolean
}

interface ObjectRow {
  readonly index: number
  readonly tag: string
}

interface SlotRow {
  readonly dep: ObjectRow | null
  readonly index: number
  readonly key: string
  readonly obj: ObjectRow
  readonly ref: string
}

/** The corpus's fact combinations are written as `origin/forced/stable/equivalent`. */
const factsKey = (facts: SpecialFacts): string =>
  `${facts.origin}/${facts.forced}/${facts.dependenciesStable}/${facts.equivalent}`

/** Compares `chooseSpecial` with Lean's `choose` on all 24 combinations of facts; returns the
 * combinations Lean's `Reachable` admits. */
async function checkDecisions(oracle: Oracle): Promise<Set<string>> {
  const rows = await oracleCorpus(oracle, 'SpecialDecision', 24, 64 * 1024)
  const reachable = new Set<string>()
  for (const line of rows) {
    const row = jsonObject(JSON.parse(line))
    const { dependenciesStable, equivalent, forced, origin } = row
    assert.ok(
      typeof dependenciesStable === 'boolean' &&
        typeof equivalent === 'boolean' &&
        typeof forced === 'boolean' &&
        (origin === 'base' || origin === 'copy' || origin === 'untracked'),
    )
    const facts: SpecialFacts = { dependenciesStable, equivalent, forced, origin }
    assert.equal(chooseSpecial(facts), row.decision, factsKey(facts))
    if (row.reachable === true) reachable.add(factsKey(facts))
  }
  return reachable
}

const TEMPORAL = Reflect.get(globalThis, 'Temporal') as
  { PlainDate: { from: (text: string) => object } } | undefined

/** The values of `current`, by index; a view or `searchParams` after the value it belongs to. */
function originals(values: readonly ValueRow[]): unknown[] {
  const built: unknown[] = []
  const owner = (index: number): number =>
    values.findIndex((value) => value.native === 'url' && value.dep === index)
  for (const [index, value] of values.entries()) {
    if (value.native === 'date') built[index] = new Date(1000)
    else if (value.native === 'buffer')
      built[index] = Uint8Array.from([1, 2, 3, 4, 5, 6, 7, 8]).buffer
    else if (value.native === 'url') built[index] = new URL('https://example.com/a?x=1')
    else if (value.native === 'params' && owner(index) === -1)
      built[index] = new URLSearchParams('x=1')
    else if (value.native === 'temporal') built[index] = TEMPORAL!.PlainDate.from('2020-01-01')
  }
  for (const [index, value] of values.entries()) {
    if (value.native === 'uint8')
      built[index] = new Uint8Array(built[value.dep!] as ArrayBuffer, 2, 4)
    else if (value.native === 'dataview')
      built[index] = new DataView(built[value.dep!] as ArrayBuffer, 1, 6)
    else if (value.native === 'params' && owner(index) !== -1)
      built[index] = (built[owner(index)] as URL).searchParams
  }
  return built
}

/** The content a value of `current` must still have after `produce`. */
function content(native: string, value: unknown): string {
  if (native === 'date') return String((value as Date).getTime())
  if (native === 'buffer') return new Uint8Array(value as ArrayBuffer).join()
  if (native === 'url') return (value as URL).href
  if (native === 'params') return (value as URLSearchParams).toString()
  return String(value)
}

/** Changes a copy's own content, and with `restore` changes it back. */
function change(native: string, copy: unknown, restore: boolean): void {
  if (native === 'date') {
    const date = copy as Date
    const time = date.getTime()
    date.setTime(time + 1)
    if (restore) date.setTime(time)
  } else if (native === 'buffer') {
    const bytes = new Uint8Array(copy as ArrayBuffer)
    bytes[3] ^= 0xff
    if (restore) bytes[3] ^= 0xff
  } else if (native === 'params') {
    const parameters = copy as URLSearchParams
    parameters.append('z', '1')
    if (restore) parameters.delete('z')
  } else if (native === 'url') {
    const url = copy as URL
    url.pathname = '/b'
    if (restore) url.pathname = '/a'
  } else assert.fail(`no change for ${native}`)
}

/** Runs one scenario through `produce` and compares each slot with Lean's resolution. */
function checkRow(library: Library, row: Record<string, unknown>): number {
  const values = row.values as ValueRow[]
  const reads = (row.reads as unknown[]).map((index) => integerIn(index, 0, values.length - 1))
  const slots = row.slots as SlotRow[]
  const label = JSON.stringify({
    reads,
    shape: row.shape,
    slots: slots.map((slot) => slot.key),
    values,
  })
  const own = originals(values)
  const before = values.map((value, index) => content(value.native, own[index]))
  const current: Record<string, unknown> = {}
  for (const [index, value] of values.entries())
    if (value.native !== 'authored') current[`v${index}`] = own[index]
  const copies: unknown[] = []
  const made: unknown[] = []
  const result = library.produce(current, (draft) => {
    for (const index of reads) copies[index] = draft[`v${index}`]
    // A dependency read with its owner is the copy the owner's copy holds.
    for (const [index, value] of values.entries()) {
      if (value.dep === null || value.native === 'authored' || copies[index] === undefined) continue
      const linked =
        value.native === 'url'
          ? (copies[index] as URL).searchParams
          : (copies[index] as ArrayBufferView).buffer
      if (copies[value.dep] === undefined) copies[value.dep] = linked
      else assert.equal(copies[value.dep], linked, `linked copies: ${label}`)
    }
    for (const [index, value] of values.entries()) {
      if (value.edit) change(value.native, copies[index], false)
      if (value.touch) change(value.native, copies[index], true)
      if (value.native === 'authored')
        made[index] = new Uint8Array(copies[value.dep!] as ArrayBuffer, 2, 4)
    }
    for (const [index, value] of values.entries())
      if (value.native !== 'authored' && !slots.some((slot) => slot.key === `v${index}`))
        Reflect.deleteProperty(draft, `v${index}`)
    for (const slot of slots) {
      if (slot.key.startsWith('v')) continue
      const value =
        slot.ref === 'copy'
          ? copies[slot.index]
          : values[slot.index].native === 'authored'
            ? made[slot.index]
            : own[slot.index]
      assert.ok(value !== undefined, `slot value: ${label}`)
      draft[slot.key] = value
    }
    return draft
  })
  for (const [index, value] of values.entries())
    if (value.native !== 'authored')
      assert.equal(content(value.native, own[index]), before[index], `current changed: ${label}`)
  const known = new Set<unknown>(
    [...own, ...copies, ...made].filter((value) => value !== undefined),
  )
  const fresh = new Map<number, unknown>()
  const classify = (value: unknown, index: number): ObjectRow => {
    const itself = values[index].native === 'authored' ? made[index] : own[index]
    if (value === itself) return { index, tag: 'value' }
    if (copies[index] !== undefined && value === copies[index]) return { index, tag: 'copy' }
    assert.ok(!known.has(value), `a fresh copy is new: ${label}`)
    const seen = fresh.get(index)
    if (seen === undefined) fresh.set(index, value)
    else assert.equal(value, seen, `one fresh copy per value: ${label}`)
    return { index, tag: 'fresh' }
  }
  for (const slot of slots) {
    const value = result[slot.key]
    const kept = classify(value, slot.index)
    const dependency = values[slot.index].dep
    const keptDependency =
      dependency === null
        ? null
        : classify(
            values[slot.index].native === 'url'
              ? (value as URL).searchParams
              : (value as ArrayBufferView).buffer,
            dependency,
          )
    assert.deepEqual(
      { dep: keptDependency, obj: kept },
      { dep: slot.dep, obj: slot.obj },
      `slot ${slot.key} of ${label}`,
    )
  }
  return slots.length
}

/** Compares `chooseSpecial` with Lean's `choose`, then each `produce` scenario's result objects
 * with Lean's `resolve` and `depOf`, recording the facts of every decision `produce` made. */
export async function checkSpecialValuesRuntime(oracle: Oracle): Promise<void> {
  const reachable = await checkDecisions(oracle)
  const library = (await bundleWithHooks(
    "export * from './src/index'",
    /graph[\\/]provenance\.ts$/,
    HOOKS,
  )) as Library
  // 658 scenarios: a date, a standalone `URLSearchParams` and a Temporal value; a buffer with two
  // views and a view the recipe makes; a URL with its `searchParams` in both index orders.
  const rows = await oracleCorpus(oracle, 'SpecialValues', 658, 4 * 1024 * 1024)
  const reached = new Map<string, number>()
  const recorder: Recorder = (facts) => {
    const key = factsKey(facts)
    reached.set(key, (reached.get(key) ?? 0) + 1)
  }
  let slots = 0
  let skipped = 0
  Reflect.set(globalThis, RECORDER, recorder)
  try {
    for (const line of rows) {
      const row = jsonObject(JSON.parse(line))
      if (row.shape === 'temporal' && TEMPORAL === undefined) skipped += 1
      else slots += checkRow(library, row)
    }
  } finally {
    Reflect.deleteProperty(globalThis, RECORDER)
  }
  // `specialFacts` produces only the combinations `facts_reachable` admits, and the corpus
  // reaches every one of them.
  for (const key of reached.keys()) assert.ok(reachable.has(key), `unreachable facts: ${key}`)
  assert.equal(reached.size, reachable.size, 'the corpus reaches every reachable combination')
  console.log(
    `SpecialValues Lean/native bridge: 24 decisions equal; ${rows.length - skipped} produce ` +
      `scenarios, ${slots} result slots and their dependencies equal` +
      (skipped === 0 ? '' : `; ${skipped} Temporal scenarios skipped without Temporal`) +
      `; produce made ${[...reached.values()].reduce((sum, count) => sum + count, 0)} decisions ` +
      `over all ${reachable.size} reachable fact combinations and no other`,
  )
}
