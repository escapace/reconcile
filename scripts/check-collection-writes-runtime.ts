// Runs `reconcile` on a kept `Map` or `Set` for every case of the `CollectionWrites` corpus, from a
// bundle of the sources that records each write the collection publication makes through the
// built-in methods, and compares the writes, in order, and the `unchanged` flag with
// `CollectionPlan.publish`'s. The collection must end holding the next entries, which Lean's writes
// reach (`publish_result`).
//
// Standalone, as the mutation audit runs it:
//   pnpm exec tsx scripts/check-collection-writes-runtime.ts
import assert from 'node:assert/strict'
import { bundleWithHooks, type Hook } from './esbuild'
import { jsonBoolean, jsonObject, oracleCorpus, type Oracle } from './lean-oracle'

type Library = typeof import('../src/index')

const RECORDER = '__reconcileCollectionWrites'

/** A collection publication writes only through its kind's `access`, whose `put` and `remove` are
 * the built-in `set` or `add` and `delete`: the first hook wraps them to record each call, before
 * it runs, with its target. The second records the `unchanged` flag publication reports. */
const HOOKS: readonly Hook[] = [
  [
    "): Pick<NativePolicy, 'aligned' | 'matches' | 'publish'> {\n",
    `  access = ((built) => ({
    ...built,
    put(target, key, value) {
      globalThis.${RECORDER}?.write(target, 'put', [key, value])
      return built.put(target, key, value)
    },
    remove(target, key) {
      globalThis.${RECORDER}?.write(target, 'delete', [key])
      return built.remove(target, key)
    },
  }))(access)\n`,
  ],
  [
    '      if (note !== undefined) note.unchanged = unchanged\n',
    `      globalThis.${RECORDER}?.published(current, unchanged)\n`,
  ],
]

/** The keys by label. SameValueZero, which the runtime compares keys with, tells them apart: `NaN`
 * among them, and a function, an atom compared by identity. */
const KEYS: readonly unknown[] = [Number.NaN, 0, 'a', () => 0]
/** A `Map`'s values by label, which only `Object.is`, as the runtime compares values, tells apart. */
const VALUES: readonly unknown[] = [0, -0]
/** The labels of an entry's slots: its key, then a `Map` entry's value. */
const SLOTS = [KEYS, VALUES]

/** The label of the value in slot `slot`. */
function labelOf(value: unknown, slot: number): number {
  const label = SLOTS[slot].findIndex((known) => Object.is(known, value))
  assert.ok(label >= 0, `unlabelled value in slot ${slot}`)
  return label
}

/** The labels of the first `width` slots of what was written or read. */
const labels = (slots: readonly unknown[], width: number): number[] =>
  slots.slice(0, width).map(labelOf)

/** A collection kind: how a case's entries are built and the result's entries read, as slots. */
interface Kind {
  readonly width: number
  build: (entries: readonly number[][]) => Iterable<unknown>
  entries: (collection: Iterable<unknown>) => unknown[][]
}

const KINDS: Readonly<Record<string, Kind | undefined>> = {
  map: {
    width: 2,
    build: (entries) => new Map(entries.map((entry) => [KEYS[entry[0]], VALUES[entry[1]]])),
    entries: (collection) => [...collection] as unknown[][],
  },
  set: {
    width: 1,
    build: (entries) => new Set(entries.map((entry) => KEYS[entry[0]])),
    entries: (collection) => [...collection].map((member) => [member]),
  },
}

/** What the publications of one call recorded: each write, as its operation and the slots it
 * passed, and each `unchanged` flag, with the collection each reached. */
interface Log {
  published: Array<{ readonly target: object; readonly unchanged: boolean }>
  writes: Array<{ readonly op: string; readonly slots: unknown[]; readonly target: object }>
}

/** One case of the corpus. */
interface Row {
  readonly current: number[][]
  readonly kind: Kind
  readonly next: number[][]
  readonly unchanged: boolean
  readonly writes: unknown[][]
}

/** Decodes one case of the corpus. */
function rowOf(line: string): Row {
  const row = jsonObject(JSON.parse(line))
  const kind = KINDS[String(row.kind)]
  assert.ok(kind !== undefined, line)
  return {
    current: row.current as number[][],
    kind,
    next: row.next as number[][],
    unchanged: jsonBoolean(row.unchanged),
    writes: row.writes as unknown[][],
  }
}

/** Reconciles an object holding the case's current collection with one holding its next, and
 * returns the current collection, which the result must keep. */
function reconcileCase(library: Library, log: Log, { current, kind, next }: Row): object {
  log.published = []
  log.writes = []
  const collection = kind.build(current)
  const holder = { collection }
  assert.equal(library.reconcile(holder, { collection: kind.build(next) }), holder)
  assert.equal(holder.collection, collection)
  return collection
}

/** Compares one case's writes, flag and result with Lean's. */
function checkLine(library: Library, log: Log, line: string): Row {
  const row = rowOf(line)
  const width = row.kind.width
  const collection = reconcileCase(library, log, row)
  const targets = [...log.published, ...log.writes].map((record) => record.target)
  assert.ok(
    targets.every((target) => target === collection),
    `a write to another object: ${line}`,
  )
  const writes = log.writes.map((write) => [write.op, ...labels(write.slots, width)])
  assert.deepEqual(writes, row.writes, `writes: ${line}`)
  assert.deepEqual(
    log.published.map((record) => record.unchanged),
    [row.unchanged],
    `unchanged: ${line}`,
  )
  const entries = row.kind.entries(collection as Iterable<unknown>)
  assert.deepEqual(
    entries.map((slots) => labels(slots, width)),
    row.next,
    `entries: ${line}`,
  )
  return row
}

/** The totals the summary reports. */
interface Totals {
  deletes: number
  maps: number
  moved: number
  puts: number
  unchanged: number
}

/** Adds one case's writes to the totals; an entry moves when a key it deletes is put again. */
function tally(totals: Totals, { kind, unchanged, writes }: Row): void {
  const deleted = writes.filter((write) => write[0] === 'delete').map((write) => write[1])
  const puts = writes.filter((write) => write[0] === 'put')
  totals.deletes += deleted.length
  totals.puts += puts.length
  totals.moved += puts.filter((write) => deleted.includes(write[1])).length
  totals.unchanged += Number(unchanged)
  totals.maps += Number(kind.width === 2)
}

/** Compares every collection publication of the corpus with Lean's `CollectionPlan.publish`. */
export async function checkCollectionWritesRuntime(oracle: Oracle): Promise<void> {
  const library = (await bundleWithHooks(
    "export * from './src/index'",
    /types[\\/]shared[\\/]collection\.ts$/,
    HOOKS,
  )) as Library
  // A Set's lists of up to four distinct keys of four, 65 · 65; a Map's of up to three, each
  // holding one of two values, 249 · 249.
  const lines = await oracleCorpus(oracle, 'CollectionWrites', 66_226, 32 * 1024 * 1024)
  const log: Log = { published: [], writes: [] }
  const totals: Totals = { deletes: 0, maps: 0, moved: 0, puts: 0, unchanged: 0 }
  Reflect.set(globalThis, RECORDER, {
    published: (target: object, unchanged: boolean) => log.published.push({ target, unchanged }),
    write: (target: object, op: string, slots: unknown[]) => log.writes.push({ op, slots, target }),
  })
  try {
    for (const line of lines) tally(totals, checkLine(library, log, line))
  } finally {
    Reflect.deleteProperty(globalThis, RECORDER)
  }
  console.log(
    `Collection-writes Lean/native bridge: ${lines.length - totals.maps} Set and ${totals.maps} ` +
      `Map publications by reconcile make Lean's writes in order, ${totals.deletes} deletes and ` +
      `${totals.puts} sets and adds (${totals.moved} of these moving an entry), report Lean's ` +
      `unchanged flag (${totals.unchanged} unchanged) and keep the collection, holding the next ` +
      'entries',
  )
}

if (process.argv[1]?.endsWith('check-collection-writes-runtime.ts')) {
  const { startOracle } = await import('./lean-oracle')
  const oracle = await startOracle()
  await checkCollectionWritesRuntime(oracle.run).finally(oracle.close)
}
