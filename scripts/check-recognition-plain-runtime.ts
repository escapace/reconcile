import assert from 'node:assert/strict'
import { checkRealChains } from './check-atoms-runtime'
import { integerIn, jsonObject, oracleCorpus, type Oracle } from './lean-oracle'
import { ARRAY_BUFFER_KIND } from '../src/types/array-buffer'
import { DATA_VIEW_KIND } from '../src/types/data-view'
import { DATE_KIND } from '../src/types/date'
import { MAP_KIND } from '../src/types/map'
import { OBJECT_KIND } from '../src/types/object'
import { SET_KIND } from '../src/types/set'
import { TEMPORAL_KIND } from '../src/types/temporal'
import { TYPED_ARRAY_KIND } from '../src/types/typed-array'
import { URL_KIND } from '../src/types/url'
import { URL_SEARCH_PARAMS_KIND } from '../src/types/url-search-parameters'
import { publicationTypes } from '../src/types/builtins'
import { orderedScan } from './recognition-scan'

/** Kinds at ranks 1 to 10, in recognition order. */
export const ranked = [
  DATE_KIND,
  MAP_KIND,
  SET_KIND,
  ARRAY_BUFFER_KIND,
  DATA_VIEW_KIND,
  TYPED_ARRAY_KIND,
  TEMPORAL_KIND,
  URL_KIND,
  URL_SEARCH_PARAMS_KIND,
  OBJECT_KIND,
]

/** The real chains of `RecognitionPlainOracle.tails`, from the first prototype to `null`, in its
 * order; the last entry stands for the throwing read. */
const typedArrayPrototype = Object.getPrototypeOf(Uint8Array.prototype) as object
export const tails: ReadonlyArray<readonly object[]> = [
  [],
  [Object.prototype],
  ...[Date, Map, Set, ArrayBuffer, DataView].map((constructor) => [
    constructor.prototype as object,
    Object.prototype,
  ]),
  [Uint8Array.prototype, typedArrayPrototype, Object.prototype],
  [URL.prototype, Object.prototype],
  [URLSearchParams.prototype, Object.prototype],
  [],
]
const RAISING_TAIL = 10

const thrown = new Error('prototype read')

/** Prototype reads of the object itself and of its custom prototypes, counted apart. */
interface Reads {
  count: number
  own: number
}

/** A prototype level whose own prototype reads are counted and, if `throws`, fail. */
function level(prototype: object | null, reads: { count: number }, throws: boolean): object {
  return new Proxy(Object.create(prototype) as object, {
    getPrototypeOf(target) {
      reads.count += 1
      if (throws) throw thrown
      return Reflect.getPrototypeOf(target)
    },
  })
}

/** The first prototype of a tail, or `null` for the empty chain. */
const first = (tail: readonly object[]): object | null => tail[0] ?? null

/** The view an object is, if any: a `Uint8Array` or a `DataView`. */
interface View {
  brand: boolean
  foreign: boolean
  typed: boolean
}

/** An object behind `depth` custom prototypes that count their reads; on the throwing tail the
 * read after them throws. A branded object is a `Uint8Array` or a `DataView`, which a proxy would
 * lose, over a buffer whose prototype is `null` when `foreign`. */
function build(depth: number, tail: number, view: View, reads: Reads): object {
  // Levels count from the deepest custom prototype, created first, to the object at `depth`; on
  // the throwing tail the deepest level's read throws.
  const throwing = tail === RAISING_TAIL ? 0 : -1
  let prototype = first(tails[tail])
  for (let index = 0; index < depth; index++)
    prototype = level(prototype, reads, index === throwing)
  return view.brand
    ? (Object.setPrototypeOf(branded(view), prototype) as object)
    : level(prototype, ownReads(reads), depth === throwing)
}

/** A `Uint8Array` or a `DataView` over a buffer whose prototype is `null` when `foreign`. */
function branded(view: View): ArrayBufferView {
  const buffer = new ArrayBuffer(1)
  if (view.foreign) Object.setPrototypeOf(buffer, null)
  return view.typed ? new Uint8Array(buffer) : new DataView(buffer)
}

/** A counter that adds the object's own reads to `own`. */
const ownReads = (reads: Reads): { count: number } => ({
  get count() {
    return reads.own
  },
  set count(value: number) {
    reads.own = value
  },
})

/** Runs one recognition, reporting its kind or that it threw the prototype read's error. */
function attempt(run: () => unknown): unknown {
  try {
    return run()
  } catch (error) {
    assert.equal(error, thrown, 'the prototype read error propagates')
    return thrown
  }
}

/** Each known-kind check on a fresh object matches Lean's recognition bounded at that rank. */
function checkKnown(row: Record<string, unknown>, depth: number, tail: number, view: View): void {
  assert.ok(Array.isArray(row.known) && row.known.length === ranked.length)
  for (const [index, expected] of row.known.entries()) {
    const matched = attempt(() =>
      publicationTypes.matches(ranked[index], build(depth, tail, view, { count: 0, own: 0 })),
    )
    assert.equal(
      matched,
      row.raised === true ? thrown : expected,
      `known-kind check at rank ${index + 1}`,
    )
  }
}

/** The custom prototypes' reads of the ordered scan: the walks from the object's prototype,
 * which built-in recognition repeats, while it reads the object itself once. */
function scannedReads(depth: number, tail: number, view: View): number {
  const scanned = { count: 0, own: 0 }
  attempt(() => orderedScan.recognize(build(depth, tail, view, scanned)))
  return scanned.count
}

/** The object is read once; its custom prototypes as the ordered scan reads them. */
function checkReads(
  row: Record<string, unknown>,
  depth: number,
  tail: number,
  view: View,
  reads: Reads,
): void {
  // A branded object cannot be proxied, so only a proxied object reports its one own read.
  assert.equal(reads.own, Number(!view.brand), 'reads of the object itself')
  const expected = row.plain === true ? 0 : scannedReads(depth, tail, view) - repeated(row, view)
  assert.equal(reads.count, expected, 'reads of its custom prototypes')
}

/** The custom prototypes' reads of the scan's walk for `DataView` in the typed-array probe, which
 * the failed `DataView` probe already decided: one per custom prototype once that probe runs its
 * walks, for a typed array over a recognized buffer. */
function repeated(row: Record<string, unknown>, view: View): number {
  const walks = view.typed && !view.foreign && (row.selected as number) >= 6
  return walks ? (row.depth as number) : 0
}

/** The view a row describes; a typed array also holds the view brand. */
function viewOf(row: Record<string, unknown>): View {
  const { brand, foreign, typed } = row
  assert.ok(typeof brand === 'boolean' && typeof foreign === 'boolean')
  assert.ok(typeof typed === 'boolean' && (brand || !typed))
  return { brand, foreign, typed }
}

/** Compares one Lean recognition with the runtime recognizer, its reads and each known-kind
 * check. */
function checkRow(row: Record<string, unknown>): void {
  const depth = integerIn(row.depth, 0, 2)
  const tail = integerIn(row.tail, 0, tails.length - 1)
  assert.ok(typeof row.raised === 'boolean' && typeof row.plain === 'boolean')
  const view = viewOf(row)
  const reads = { count: 0, own: 0 }
  const kind = attempt(() => publicationTypes.recognize(build(depth, tail, view, reads)))
  const expected = row.raised ? thrown : ranked[integerIn(row.selected, 1, 10) - 1]
  assert.equal(kind, expected, 'recognized kind')
  checkReads(row, depth, tail, view, reads)
  checkKnown(row, depth, tail, view)
}

/** Compares built-in recognition with Lean's `Types.RecognitionPlain.recognize`. */
export async function checkRecognitionPlainRuntime(oracle: Oracle): Promise<void> {
  checkRealChains(tails)
  // 11 tails behind zero to two custom prototypes, without a view brand and as a typed array or a
  // `DataView` over a recognized or a foreign buffer; a branded object cannot throw on its own read.
  const rows = await oracleCorpus(oracle, 'RecognitionPlain', 161, 64 * 1024)
  for (const line of rows) checkRow(jsonObject(JSON.parse(line)))
  console.log(
    `RecognitionPlain Lean/native bridge: ${rows.length} prototype chains, full recognition and ` +
      `${rows.length * ranked.length} known-kind checks`,
  )
}
