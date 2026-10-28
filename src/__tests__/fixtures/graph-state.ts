import { assert } from 'vitest'
import { isReconcileError, reconcile } from '../../index'

/**
 * What a graph holds: every object it reaches, in first-visit order, and a text of their
 * contents in which an object, function or symbol is its index. Contents are own keys in order
 * with their attributes, data values and accessor functions, the values getters return, the
 * prototype and extensibility, entries of a `Map` and members of a `Set` in order, a date's time,
 * a buffer's bytes, a view's type, buffer and range, and a URL's or `URLSearchParams`' text.
 * Prototypes and functions are compared by identity only.
 */
export interface GraphState {
  readonly objects: readonly unknown[]
  readonly text: string
}

/** Reads the state of the graph `root` reaches, running its getters once each. */
export function graphState(root: unknown): GraphState {
  const objects: unknown[] = []
  const ids = new Map<unknown, number>()
  const contents: unknown[] = []
  const pending: object[] = []
  // Prototypes, functions and symbols: identity only.
  const identity = (value: unknown): number => {
    let id = ids.get(value)
    if (id === undefined) {
      id = objects.length
      ids.set(value, id)
      objects.push(value)
      contents.push('identity')
    }
    return id
  }
  const encode = (value: unknown): unknown => {
    if (typeof value === 'function' || typeof value === 'symbol') return { id: identity(value) }
    if (typeof value === 'object' && value !== null) {
      let id = ids.get(value)
      if (id === undefined) {
        id = objects.length
        ids.set(value, id)
        objects.push(value)
        contents.push(undefined)
        pending.push(value)
      }
      return { ref: id }
    }
    if (typeof value === 'number') return { n: Object.is(value, -0) ? '-0' : String(value) }
    if (typeof value === 'bigint') return { big: String(value) }
    return value === undefined ? { undef: true } : value
  }
  const properties = (o: object): unknown[] =>
    Reflect.ownKeys(o).map((key) => {
      const d = Reflect.getOwnPropertyDescriptor(o, key)!
      const head = [encode(key), d.enumerable, d.configurable]
      if ('value' in d) return [...head, d.writable, encode(d.value as unknown)]
      const got: unknown = d.get === undefined ? undefined : Reflect.get(o, key)
      return [...head, encode(d.get), encode(d.set), encode(got)]
    })
  const describe = (o: object): unknown => {
    const prototype = Reflect.getPrototypeOf(o)
    const common = [prototype === null ? null : identity(prototype), Reflect.isExtensible(o)]
    if (o instanceof Date) return [...common, 'date', o.getTime(), properties(o)]
    if (o instanceof ArrayBuffer) return [...common, 'buffer', [...new Uint8Array(o)]]
    if (ArrayBuffer.isView(o)) {
      const type = prototype?.constructor.name ?? 'view'
      return [...common, type, encode(o.buffer), o.byteOffset, o.byteLength]
    }
    if (o instanceof Map)
      return [...common, 'map', [...o].map(([k, v]) => [encode(k), encode(v)]), properties(o)]
    if (o instanceof Set) return [...common, 'set', [...o].map(encode), properties(o)]
    if (o instanceof URL) return [...common, 'url', o.href, encode(o.searchParams), properties(o)]
    if (o instanceof URLSearchParams) return [...common, 'parameters', String(o), properties(o)]
    return [...common, Array.isArray(o) ? 'array' : 'object', properties(o)]
  }
  encode(root)
  for (let at = 0; at < pending.length; at += 1) {
    const o = pending[at]
    contents[ids.get(o)!] = describe(o)
  }
  return { objects, text: JSON.stringify(contents) }
}

/** Asserts that a graph holds the same objects in the same places with the same contents. */
export function assertSameState(before: GraphState, after: GraphState, label = 'graph'): void {
  assert.equal(after.text, before.text, `${label}: contents changed`)
  assert.equal(after.objects.length, before.objects.length, `${label}: objects changed`)
  for (let index = 0; index < before.objects.length; index += 1)
    assert.ok(Object.is(after.objects[index], before.objects[index]), `${label}: object ${index}`)
}

/** Asserts that `reconcile(current, next)` throws `PublicationWouldChangeNext` and leaves both
 * arguments as they were. */
export function assertWouldChangeNext(current: unknown, next: unknown): void {
  const currentBefore = graphState(current)
  const nextBefore = graphState(next)
  let error: unknown
  try {
    reconcile(current, next)
  } catch (caught) {
    error = caught
  }
  assert.ok(isReconcileError(error), 'expected a ReconcileError')
  assert.deepEqual(error.cause, { type: 'PublicationWouldChangeNext' })
  assertSameState(currentBefore, graphState(current), 'current')
  assertSameState(nextBefore, graphState(next), 'next')
}

/** What `reconcileKeepingNext` returns for a call rejected with `PublicationWouldChangeNext`. */
export const WOULD_CHANGE_NEXT: unique symbol = Symbol('would change next')

/** Runs `reconcile(current, next)` and checks that `next` keeps its state whatever the outcome,
 * and that a `PublicationWouldChangeNext` rejection leaves `current` as it was too, as one decided
 * before any write does: the result, or `WOULD_CHANGE_NEXT` for that rejection. Other errors
 * propagate. Reads each getter of both arguments before and after the call. */
export function reconcileKeepingNext<T>(current: unknown, next: T): T | typeof WOULD_CHANGE_NEXT {
  const currentBefore = graphState(current)
  const nextBefore = graphState(next)
  let result: T
  try {
    result = reconcile(current, next)
  } catch (error) {
    if (!isReconcileError(error) || error.cause.type !== 'PublicationWouldChangeNext') throw error
    assertSameState(currentBefore, graphState(current), 'current')
    assertSameState(nextBefore, graphState(next), 'next')
    return WOULD_CHANGE_NEXT
  }
  assertSameState(nextBefore, graphState(next), 'next')
  return result
}
