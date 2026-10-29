import assert from 'node:assert/strict'
import { checkRealChains } from './atoms'
import { integerIn, jsonBoolean, jsonObject, oracleCorpus, type Oracle } from '../oracle'
import { recognize } from '../../../src/adapters/recognition'
import { ATOM_KIND } from '../../../src/constants'
import type { PrototypeRead } from '../../../src/types'
import { publicationTypes } from '../../../src/types/builtins'
import { OBJECT_KIND } from '../../../src/types/object'
import {
  attempt,
  branded,
  level,
  ranked,
  tails as recognitionTails,
  thrown,
  type Reads,
  type View,
} from './recognition-plain'

/** The real chains of `IngressOracle.tails`, from the first prototype to `null`, in its order:
 * the RecognitionPlain bridge's chains before its throwing read, then listed ones; the last entry
 * stands for the throwing read. */
const tails: ReadonlyArray<readonly object[]> = [
  ...recognitionTails.slice(0, -1),
  ...[RegExp, Error, Promise, Blob].map((constructor) => [
    constructor.prototype as object,
    Object.prototype,
  ]),
  [TypeError.prototype, Error.prototype, Object.prototype],
  [],
]
const RAISING_TAIL = 15

/** `depth` custom prototypes over a tail that count their reads in `reads.count`; on the
 * throwing tail the deepest one's read throws. */
function custom(depth: number, tail: number, reads: Reads): object | null {
  let prototype: object | null = tails[tail][0] ?? null
  for (let index = 0; index < depth; index++)
    prototype = level(prototype, () => (reads.count += 1), index === 0 && tail === RAISING_TAIL)
  return prototype
}

/** The typed array an object is, if any: a `Uint8Array` over a buffer whose prototype is `null`
 * when `foreign` and whose prototype's prototype read throws when `raises`. */
type Brand = Omit<View, 'typed'>

/** An object behind `depth` custom prototypes; with none, its own read throws on the throwing
 * tail. A branded object is a `Uint8Array`, which a proxy would lose. */
function build(depth: number, tail: number, view: Brand, reads: Reads): object {
  const prototype = custom(depth, tail, reads)
  if (view.brand)
    return Object.setPrototypeOf(branded({ ...view, typed: true }), prototype) as object
  return level(prototype, () => (reads.own += 1), depth === 0 && tail === RAISING_TAIL)
}

/** Runs one ingress on a fresh object, reporting its kind, or the prototype read's error, and the
 * reads it made. */
function ingress(
  depth: number,
  tail: number,
  view: Brand,
  read: PrototypeRead | undefined,
): { kind: unknown; reads: Reads } {
  const reads = { count: 0, own: 0 }
  const value = build(depth, tail, view, reads)
  return { kind: attempt(() => recognize(publicationTypes, value, read)), reads }
}

/** The kind Lean's outcome names. */
function expectedKind(row: Record<string, unknown>): unknown {
  if (row.outcome === 'raised') return thrown
  if (row.outcome === 'atom') return ATOM_KIND
  if (row.outcome === 'object') return OBJECT_KIND
  assert.equal(row.outcome, 'structural')
  return ranked[integerIn(row.rank, 1, 9) - 1]
}

/** The typed array a row describes, if any; only a branded object has a foreign or raising
 * buffer. */
function brandOf(row: Record<string, unknown>): Brand {
  const view = {
    brand: jsonBoolean(row.brand),
    foreign: jsonBoolean(row.foreign),
    raises: jsonBoolean(row.bufferRaises),
  }
  assert.ok(view.brand || (!view.foreign && !view.raises))
  return view
}

/** Compares one Lean ingress with the runtime, sharing the prototype read and not. */
function checkRow(row: Record<string, unknown>): boolean {
  const depth = integerIn(row.depth, 0, 2)
  const tail = integerIn(row.tail, 0, tails.length - 1)
  const view = brandOf(row)
  const shared = ingress(depth, tail, view, { known: false, prototype: null })
  const separate = ingress(depth, tail, view, undefined)
  const kind = expectedKind(row)
  assert.equal(shared.kind, kind, 'kind with the prototype read shared')
  assert.equal(separate.kind, kind, 'kind with a separate atom split')
  // A branded object cannot be proxied, so only a proxied object reports its own reads.
  if (!view.brand) {
    assert.equal(shared.reads.own, integerIn(row.shared, 0, 2), 'own reads, shared')
    assert.equal(separate.reads.own, integerIn(row.separate, 0, 2), 'own reads, separate')
  }
  // Sharing the first read leaves the walk over the custom prototypes as it was.
  assert.equal(shared.reads.count, separate.reads.count, 'reads of the custom prototypes')
  return shared.reads.own < separate.reads.own
}

/** Compares shared-read ingress with Lean's `Types.Ingress.ingress`. */
export async function checkIngressRuntime(oracle: Oracle): Promise<void> {
  checkRealChains(tails)
  // 16 tails behind zero to two custom prototypes, without a view brand and as a typed array over
  // a recognized, a foreign and a raising buffer; a branded object cannot throw on its own read.
  const rows = await oracleCorpus(oracle, 'Ingress', 189, 128 * 1024)
  let saved = 0
  for (const line of rows) if (checkRow(jsonObject(JSON.parse(line)))) saved += 1
  console.log(
    `Ingress Lean/native bridge: ${rows.length} prototype chains, each object read once with the ` +
      `read shared; ${saved} fallbacks read twice by a separate atom split`,
  )
}
