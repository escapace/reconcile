import { isNode } from './graph/edge'
import { noValue } from './types/shared/empty'
import { traverse } from './publication/capture'
import type { Edge, Layout, SnapshotWrite, SnapshotRegistry } from './types'
import { snapshotTypes } from './types/builtins'

/**
 * Owns pending or initialized snapshot state on the canonical traversal reference.
 *
 * @remarks
 * Initialization completes before the target enters the public memo. There is no parallel
 * writer table; SnapshotOwner proves the finite installation/resolution trace correspondence.
 */
class SnapshotReference {
  declare layout: Layout | undefined
  declare readonly node: number
  declare target: object | undefined
  declare write: SnapshotWrite | undefined

  constructor(node: number) {
    this.node = node
    this.layout = undefined
    this.target = undefined
    this.write = undefined
  }

  initialize(layout: Layout, target: object, write: SnapshotWrite): void {
    this.layout = layout
    this.target = target
    this.write = write
  }
}

/**
 * Returns a deep copy of `value` that can be changed without affecting the original.
 *
 * @remarks
 * The copy keeps plain-object key order and prototypes, sparse-array holes, shared references,
 * cycles, the sharing between buffers and their views, and each URL's owned search parameters. Plain objects, arrays, `Map`, `Set`,
 * `Date`, `ArrayBuffer`, `DataView`, typed arrays and available Temporal values are supported,
 * including Vue reactive wrappers that behave like objects, arrays, maps or sets. Primitives are returned as they are,
 * including bigint, and functions are kept by reference. Temporal support uses the eight value
 * classes on the current global Temporal namespace, without installing a polyfill. Other
 * objects, such as class instances, are copied like plain objects: the copy has the same prototype and own properties but not private fields or
 * other internal state.
 *
 * @example
 * ```ts
 * const node = { label: 'a', children: [] as unknown[] }
 * node.children.push(node)
 * const copy = snapshot(node) as typeof node
 * // copy !== node; copy.children[0] === copy
 * ```
 *
 * @param value - The value to copy.
 * @param seen - Map from source objects already copied to their copies. Entries are used as
 * given, without checking; the copy is detached only if every entry is a detached copy of its
 * source. A supplied parameter copy that a fresh URL would need to adopt raises
 * `SnapshotURLSearchParamsMemoIncompatible`; supply a consistent owner-and-parameters pair
 * or omit those entries. Most callers omit the memo.
 * @returns A detached copy of `value`, or `value` itself when it is not an object.
 */
export function snapshot(
  value: unknown,
  seen: WeakMap<object, object> = new WeakMap<object, object>(),
): unknown {
  return snapshotWith(snapshotTypes, value, seen)
}

export function snapshotWith(
  types: SnapshotRegistry,
  value: unknown,
  seen: WeakMap<object, object>,
): unknown {
  const constructed = new WeakMap<object, object>()
  const resolve = (edge: Edge): unknown =>
    isNode(edge) ? (edge as SnapshotReference).target : edge.value
  const root = traverse<SnapshotReference>(
    types,
    value,
    {
      finish: noValue,
      begin(source, writer, layout) {
        const policy = types.policies[layout.kind]
        policy.snapshot(layout, resolve, writer)
        const response = policy.construction(layout)
        if (response !== undefined) constructed.set(writer.target!, response)
        seen.set(source, writer.target!)
      },
      constructed: (target) => constructed.get(target),
      edge(writer, child, key) {
        writer.write?.(child, key)
      },
      existing: (source) => seen.get(source),
      layout: (writer) => writer.layout,
      reserve: (node) => new SnapshotReference(node),
    },
    undefined,
    'snapshot',
  )
  return resolve(root)
}
