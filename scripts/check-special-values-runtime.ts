// Runs `chooseSpecial` on every combination of facts, and `produce` on every scenario of
// `Produce.SpecialValues` the oracle generates, against Lean's decision and resolution.
import assert from 'node:assert/strict'
import { chooseSpecial } from '../src/graph/provenance'
import type { SpecialFacts } from '../src/types'
import { bundleWithHooks, type Hook } from './esbuild'
import { integerIn, jsonBoolean, jsonObject, oracleCorpus, type Oracle } from './lean-oracle'

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

/** Narrows a corpus row's origin. */
function originOf(value: unknown): SpecialFacts['origin'] {
  assert.ok(value === 'base' || value === 'copy' || value === 'untracked')
  return value
}

/** Compares `chooseSpecial` with Lean's `choose` on all 24 combinations of facts; returns the
 * combinations Lean's `Reachable` admits. */
async function checkDecisions(oracle: Oracle): Promise<Set<string>> {
  const rows = await oracleCorpus(oracle, 'SpecialDecision', 24, 64 * 1024)
  const reachable = new Set<string>()
  for (const line of rows) {
    const row = jsonObject(JSON.parse(line))
    const facts: SpecialFacts = {
      dependenciesStable: jsonBoolean(row.dependenciesStable),
      equivalent: jsonBoolean(row.equivalent),
      forced: jsonBoolean(row.forced),
      origin: originOf(row.origin),
    }
    assert.equal(chooseSpecial(facts), row.decision, factsKey(facts))
    if (row.reachable === true) reachable.add(factsKey(facts))
  }
  return reachable
}

const TEMPORAL = Reflect.get(globalThis, 'Temporal') as
  { PlainDate: { from: (text: string) => object } } | undefined

/** Makes each value of `current` that stands alone, by kind; the recipe makes an authored view. */
const alone: Readonly<Record<string, () => unknown>> = {
  authored: () => undefined,
  buffer: () => Uint8Array.from([1, 2, 3, 4, 5, 6, 7, 8]).buffer,
  date: () => new Date(1000),
  params: () => new URLSearchParams('x=1'),
  temporal: () => TEMPORAL!.PlainDate.from('2020-01-01'),
  url: () => new URL('https://example.com/a?x=1'),
}

/** Makes each value of `current` that belongs to another, by kind, from that value: a view from its
 * buffer, a URL's `searchParams` from the URL. The recipe makes an authored view as a `uint8`. */
const belonging: Readonly<Record<string, (owner: unknown) => unknown>> = {
  dataview: (buffer) => new DataView(buffer as ArrayBuffer, 1, 6),
  params: (url) => (url as URL).searchParams,
  uint8: (buffer) => new Uint8Array(buffer as ArrayBuffer, 2, 4),
}

/** The index of the value that value `index` of `current` belongs to: a view's buffer, or the URL
 * whose `searchParams` it is; `-1` for a value that stands alone. */
function ownerOf(values: readonly ValueRow[], index: number): number {
  const { dep, native } = values[index]
  if (native === 'params')
    return values.findIndex((value) => value.native === 'url' && value.dep === index)
  return native === 'uint8' || native === 'dataview' ? dep! : -1
}

/** The values of `current`, by index; a view or `searchParams` after the value it belongs to. */
function originals(values: readonly ValueRow[]): unknown[] {
  const owners = values.map((_, index) => ownerOf(values, index))
  const built = values.map((value, index) =>
    owners[index] === -1 ? alone[value.native]() : undefined,
  )
  for (const [index, value] of values.entries())
    if (owners[index] !== -1) built[index] = belonging[value.native](built[owners[index]])
  return built
}

/** The content each value of `current` must still have after `produce`, by kind; any other value's
 * is its string. */
const contents: Readonly<Partial<Record<string, (value: unknown) => string>>> = {
  buffer: (value) => new Uint8Array(value as ArrayBuffer).join(),
  date: (value) => String((value as Date).getTime()),
  params: (value) => (value as URLSearchParams).toString(),
  url: (value) => (value as URL).href,
}

/** The content a value of `current` must still have after `produce`. */
const content = (native: string, value: unknown): string => (contents[native] ?? String)(value)

/** Changes a copy's own content, by kind, and with `restore` changes it back. */
const changes: Readonly<Partial<Record<string, (copy: unknown, restore: boolean) => void>>> = {
  buffer: (copy, restore) => {
    const bytes = new Uint8Array(copy as ArrayBuffer)
    bytes[3] ^= 0xff
    if (restore) bytes[3] ^= 0xff
  },
  date: (copy, restore) => {
    const date = copy as Date
    const time = date.getTime()
    date.setTime(time + 1)
    if (restore) date.setTime(time)
  },
  params: (copy, restore) => {
    const parameters = copy as URLSearchParams
    parameters.append('z', '1')
    if (restore) parameters.delete('z')
  },
  url: (copy, restore) => {
    const url = copy as URL
    url.pathname = '/b'
    if (restore) url.pathname = '/a'
  },
}

/** Changes a copy's own content, and with `restore` changes it back. */
function change(native: string, copy: unknown, restore: boolean): void {
  const apply = changes[native]
  if (apply === undefined) assert.fail(`no change for ${native}`)
  apply(copy, restore)
}

/** The object a value holds: a URL's `searchParams`, or a view's buffer. */
const held = (native: string, value: unknown): unknown =>
  native === 'url' ? (value as URL).searchParams : (value as ArrayBufferView).buffer

/** One scenario: the values of `current` and the result's slots, with the copies the recipe reads
 * and the views it makes, by value index. */
interface Scenario {
  readonly copies: unknown[]
  readonly label: string
  readonly made: unknown[]
  readonly own: readonly unknown[]
  readonly reads: readonly number[]
  readonly slots: readonly SlotRow[]
  readonly values: readonly ValueRow[]
}

/** Decodes one scenario and makes the values of `current`. */
function scenarioOf(row: Record<string, unknown>): Scenario {
  const values = row.values as ValueRow[]
  const reads = (row.reads as unknown[]).map((index) => integerIn(index, 0, values.length - 1))
  const slots = row.slots as SlotRow[]
  const label = JSON.stringify({
    reads,
    shape: row.shape,
    slots: slots.map((slot) => slot.key),
    values,
  })
  return { copies: [], label, made: [], own: originals(values), reads, slots, values }
}

/** Value `index` itself: the view the recipe made for an authored view, otherwise the value of
 * `current`. */
const itself = ({ made, own, values }: Scenario, index: number): unknown =>
  values[index].native === 'authored' ? made[index] : own[index]

/** The object `produce` starts from: each value of `current` but an authored view, at `v<index>`. */
function currentOf({ own, values }: Scenario): Record<string, unknown> {
  const current: Record<string, unknown> = {}
  for (const [index, value] of values.entries())
    if (value.native !== 'authored') current[`v${index}`] = own[index]
  return current
}

/** Whether a value of `current` that holds another, as a URL its `searchParams` or a view its
 * buffer, has a copy the recipe read. */
const holdsRead = (value: ValueRow, copy: unknown): boolean =>
  value.dep !== null && value.native !== 'authored' && copy !== undefined

/** A dependency read with its owner is the copy the owner's copy holds. */
function linkCopy({ copies, label, values }: Scenario, index: number): void {
  const value = values[index]
  if (!holdsRead(value, copies[index])) return
  const dependency = value.dep!
  const linked = held(value.native, copies[index])
  if (copies[dependency] === undefined) copies[dependency] = linked
  else assert.equal(copies[dependency], linked, `linked copies: ${label}`)
}

/** Reads the recipe's copies in the corpus's order, then links each dependency read with its
 * owner. */
function readCopies(scenario: Scenario, draft: Record<string, unknown>): void {
  for (const index of scenario.reads) scenario.copies[index] = draft[`v${index}`]
  for (const index of scenario.values.keys()) linkCopy(scenario, index)
}

/** Changes value `index`'s copy where the corpus edits it, changes and restores it where the
 * corpus touches it, and makes an authored view over its buffer's copy. */
function changeCopy({ copies, made, values }: Scenario, index: number): void {
  const value = values[index]
  if (value.edit) change(value.native, copies[index], false)
  if (value.touch) change(value.native, copies[index], true)
  if (value.native === 'authored') made[index] = belonging.uint8(copies[value.dep!])
}

/** Deletes the key of each value of `current` that no slot of the result keeps there. */
function dropUnkept({ slots, values }: Scenario, draft: Record<string, unknown>): void {
  for (const [index, value] of values.entries())
    if (value.native !== 'authored' && !slots.some((slot) => slot.key === `v${index}`))
      Reflect.deleteProperty(draft, `v${index}`)
}

/** Sets each slot of the result but a value's own key: to the recipe's copy, or the value
 * itself. */
function setSlots(scenario: Scenario, draft: Record<string, unknown>): void {
  for (const slot of scenario.slots) {
    if (slot.key.startsWith('v')) continue
    const value = slot.ref === 'copy' ? scenario.copies[slot.index] : itself(scenario, slot.index)
    assert.ok(value !== undefined, `slot value: ${scenario.label}`)
    draft[slot.key] = value
  }
}

/** The recipe: reads the copies, changes them value by value, and leaves the result's slots. */
function recipe(scenario: Scenario, draft: Record<string, unknown>): Record<string, unknown> {
  readCopies(scenario, draft)
  for (const index of scenario.values.keys()) changeCopy(scenario, index)
  dropUnkept(scenario, draft)
  setSlots(scenario, draft)
  return draft
}

/** `produce` leaves the content of each value of `current` as it was. */
function checkUnchanged({ label, own, values }: Scenario, before: readonly string[]): void {
  for (const [index, value] of values.entries())
    if (value.native !== 'authored')
      assert.equal(content(value.native, own[index]), before[index], `current changed: ${label}`)
}

/** The result's objects of one scenario as they are classified: every object the scenario held,
 * and the fresh copy found for each value. */
interface Resolution {
  readonly fresh: Map<number, unknown>
  readonly known: ReadonlySet<unknown>
  readonly scenario: Scenario
}

/** A fresh copy is new, and each value has at most one. */
function checkFresh({ fresh, known, scenario }: Resolution, value: unknown, index: number): void {
  assert.ok(!known.has(value), `a fresh copy is new: ${scenario.label}`)
  const seen = fresh.get(index)
  if (seen === undefined) fresh.set(index, value)
  else assert.equal(value, seen, `one fresh copy per value: ${scenario.label}`)
}

/** Classifies an object of the result as value `index` itself, the recipe's copy of it, or a
 * fresh copy. */
function classify(resolution: Resolution, value: unknown, index: number): ObjectRow {
  const { copies } = resolution.scenario
  if (value === itself(resolution.scenario, index)) return { index, tag: 'value' }
  if (copies[index] !== undefined && value === copies[index]) return { index, tag: 'copy' }
  checkFresh(resolution, value, index)
  return { index, tag: 'fresh' }
}

/** Compares a slot's object of the result, and the object it holds, with Lean's resolution. */
function checkSlot(resolution: Resolution, result: Record<string, unknown>, slot: SlotRow): void {
  const value = result[slot.key]
  const kept = classify(resolution, value, slot.index)
  const { dep, native } = resolution.scenario.values[slot.index]
  const keptDependency = dep === null ? null : classify(resolution, held(native, value), dep)
  assert.deepEqual(
    { dep: keptDependency, obj: kept },
    { dep: slot.dep, obj: slot.obj },
    `slot ${slot.key} of ${resolution.scenario.label}`,
  )
}

/** Runs one scenario through `produce` and compares each slot with Lean's resolution. */
function checkRow(library: Library, row: Record<string, unknown>): number {
  const scenario = scenarioOf(row)
  const { copies, made, own, slots, values } = scenario
  const before = values.map((value, index) => content(value.native, own[index]))
  const result = library.produce(currentOf(scenario), (draft) => recipe(scenario, draft))
  checkUnchanged(scenario, before)
  const known = new Set<unknown>(
    [...own, ...copies, ...made].filter((value) => value !== undefined),
  )
  const resolution: Resolution = { fresh: new Map(), known, scenario }
  for (const slot of slots) checkSlot(resolution, result, slot)
  return slots.length
}

/** Runs `run` with `recorder` called at the start of `chooseSpecial`. */
function recording<T>(recorder: Recorder, run: () => T): T {
  Reflect.set(globalThis, RECORDER, recorder)
  try {
    return run()
  } finally {
    Reflect.deleteProperty(globalThis, RECORDER)
  }
}

/** Checks each scenario but the Temporal ones without `Temporal`; counts the result slots checked
 * and the scenarios skipped. */
function checkScenarios(
  library: Library,
  rows: readonly string[],
): { skipped: number; slots: number } {
  let slots = 0
  let skipped = 0
  for (const line of rows) {
    const row = jsonObject(JSON.parse(line))
    if (row.shape === 'temporal' && TEMPORAL === undefined) skipped += 1
    else slots += checkRow(library, row)
  }
  return { skipped, slots }
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
  const { skipped, slots } = recording(recorder, () => checkScenarios(library, rows))
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
