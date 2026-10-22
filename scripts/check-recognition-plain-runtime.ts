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
import { builtinTypes, publicationTypes } from '../src/types/builtins'

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

/** An object behind `depth` custom prototypes that count their reads; on the throwing tail the
 * read after them throws. A branded object is a `Uint8Array`, which a proxy would lose. */
function build(depth: number, tail: number, brand: boolean, reads: Reads): object {
  // Levels count from the deepest custom prototype, created first, to the object at `depth`; on
  // the throwing tail the deepest level's read throws.
  const throwing = tail === RAISING_TAIL ? 0 : -1
  let prototype = first(tails[tail])
  for (let index = 0; index < depth; index++)
    prototype = level(prototype, reads, index === throwing)
  return brand
    ? (Object.setPrototypeOf(new Uint8Array(1), prototype) as object)
    : level(prototype, ownReads(reads), depth === throwing)
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
function checkKnown(
  row: Record<string, unknown>,
  depth: number,
  tail: number,
  brand: boolean,
): void {
  assert.ok(Array.isArray(row.known) && row.known.length === ranked.length)
  for (const [index, expected] of row.known.entries()) {
    const matched = attempt(() =>
      publicationTypes.matches(ranked[index], build(depth, tail, brand, { count: 0, own: 0 })),
    )
    assert.equal(
      matched,
      row.raised === true ? thrown : expected,
      `known-kind check at rank ${index + 1}`,
    )
  }
}

/** The custom prototypes' reads of the generic ordered scan: the walks from the object's
 * prototype, which built-in recognition repeats, while it reads the object itself once. */
function scannedReads(depth: number, tail: number, brand: boolean): number {
  const scanned = { count: 0, own: 0 }
  attempt(() => builtinTypes.recognize(build(depth, tail, brand, scanned)))
  return scanned.count
}

/** The object is read once; its custom prototypes as the generic scan reads them. */
function checkReads(row: Record<string, unknown>, depth: number, tail: number, reads: Reads): void {
  const brand = row.brand === true
  // A branded object cannot be proxied, so only a proxied object reports its one own read.
  assert.equal(reads.own, Number(!brand), 'reads of the object itself')
  // The generic typed-array probe walks the chain again for `instanceof DataView`, which the
  // failed `DataView` probe already decided.
  const repeated = brand && row.selected === 6 ? depth : 0
  assert.equal(
    reads.count,
    row.plain === true ? 0 : scannedReads(depth, tail, brand) - repeated,
    'reads of its custom prototypes',
  )
}

/** Compares one Lean recognition with the runtime recognizer, its reads and each known-kind
 * check. */
function checkRow(row: Record<string, unknown>): void {
  const depth = integerIn(row.depth, 0, 2)
  const tail = integerIn(row.tail, 0, tails.length - 1)
  assert.ok(typeof row.brand === 'boolean' && typeof row.raised === 'boolean')
  assert.ok(typeof row.plain === 'boolean')
  const reads = { count: 0, own: 0 }
  const kind = attempt(() =>
    publicationTypes.recognize(build(depth, tail, row.brand as boolean, reads)),
  )
  const expected = row.raised ? thrown : ranked[integerIn(row.selected, 1, 10) - 1]
  assert.equal(kind, expected, 'recognized kind')
  checkReads(row, depth, tail, reads)
  checkKnown(row, depth, tail, row.brand)
}

/** Compares built-in recognition with Lean's `Types.RecognitionPlain.recognize`. */
export async function checkRecognitionPlainRuntime(oracle: Oracle): Promise<void> {
  checkRealChains(tails)
  // 11 tails behind zero to two custom prototypes, with and without a view brand; a branded
  // object cannot throw on its own read.
  const rows = await oracleCorpus(oracle, 'RecognitionPlain', 65, 64 * 1024)
  for (const line of rows) checkRow(jsonObject(JSON.parse(line)))
  console.log(
    `RecognitionPlain Lean/native bridge: ${rows.length} prototype chains, full recognition and ` +
      `${rows.length * ranked.length} known-kind checks`,
  )
}
