import assert from 'node:assert/strict'
import { integerIn, jsonObject, oracleCorpus, type Oracle } from '../oracle'
import { produce } from '../../../src/produce'
import { reconcile } from '../../../src/reconcile'
import { snapshot } from '../../../src/snapshot'
import { deserialize } from '../../../src/deserialize'
import { serialize } from '../../../src/serialize'

interface Kind {
  readonly change: (value: never) => void
  readonly make: (subclass: boolean) => object
  /** Another value of the same kind by recognition: a typed array given `DataView.prototype`. */
  readonly alias?: () => object
}

class DataViewSubclass extends DataView<ArrayBuffer> {}

const kinds: ReadonlyArray<Kind | undefined> = [
  {
    change: (value: unknown[]) => {
      value[0] = 2
    },
    make: (subclass) => (subclass ? class extends Array {} : Array).from([1]),
  },
  {
    change: (value: Map<number, number>) => value.set(1, 3),
    make: (subclass) => new (subclass ? class extends Map {} : Map)([[1, 2]]),
  },
  {
    change: (value: Set<number>) => value.add(2),
    make: (subclass) => new (subclass ? class extends Set {} : Set)([1]),
  },
  {
    change: (value: Date) => value.setTime(5),
    make: (subclass) => new (subclass ? class extends Date {} : Date)(0),
  },
  {
    alias: () => Object.setPrototypeOf(new Uint8Array(2), DataView.prototype) as object,
    change: (value: DataView) => value.setUint8(0, 1),
    make: (subclass) =>
      subclass ? new DataViewSubclass(new ArrayBuffer(2)) : new DataView(new ArrayBuffer(2)),
  },
  {
    change: (value: URL) => {
      value.pathname = '/changed'
    },
    make: (subclass) => new (subclass ? class extends URL {} : URL)('https://example.test/'),
  },
  {
    change: (value: URLSearchParams) => value.append('b', '2'),
    make: (subclass) => new (subclass ? class extends URLSearchParams {} : URLSearchParams)('a=1'),
  },
  // Temporal, kind 7, is optional and left out.
  undefined,
  {
    change: (value: Uint8Array) => {
      value[0] = 9
    },
    make: (subclass) => new (subclass ? class extends Uint8Array {} : Uint8Array)([1, 2, 3, 4]),
  },
  {
    change: (value: Uint16Array) => {
      value[0] = 9
    },
    make: (subclass) => new (subclass ? class extends Uint16Array {} : Uint16Array)([1, 2]),
  },
]

/** The copies each function builds of one value: a snapshot, an object reconcile adds and a
 * produce result the recipe changed. */
function copies(kind: Kind, source: () => object): Array<[string, object, object]> {
  const snapshotted = source()
  const added = source()
  const holder: Record<string, unknown> = { value: 0 }
  reconcile(holder, { value: added })
  const changed = source()
  const produced = produce({ value: changed }, (draft) => {
    kind.change(draft.value as never)
    return draft
  })
  return [
    ['snapshot', snapshotted, (snapshot({ value: snapshotted }) as { value: object }).value],
    ['reconcile', added, holder.value as object],
    ['produce', changed, produced.value],
  ]
}

/** Serializes one value; an accepted value must come back with its prototype. */
function serializes(value: object): boolean {
  let json: unknown
  try {
    json = serialize({ value })
  } catch {
    return false
  }
  const restored = (deserialize(json, { maxBytes: Infinity }) as { value: object }).value
  assert.equal(Object.getPrototypeOf(restored), Object.getPrototypeOf(value), 'restored prototype')
  return true
}

/** Makes the value of one oracle row: an instance of `kind` or of its subclass, or, for a typed
 * array, one given another typed kind's standard prototype. */
function sourceOf(kind: Kind, row: Record<string, unknown>): () => object {
  const other = row.other === null ? undefined : kinds[integerIn(row.other, 8, 9)]!
  return () => {
    const value = kind.make(row.subclass === true)
    if (other === undefined) return value
    return Object.setPrototypeOf(
      value,
      Object.getPrototypeOf(other.make(false)) as object,
    ) as object
  }
}

/** Checks whether `serialize` accepts a row's value, and its kind's alias for an own instance. */
function checkSerializes(kind: Kind, row: Record<string, unknown>, source: () => object): void {
  assert.equal(serializes(source()), row.serializes, 'serialize')
  if (kind.alias !== undefined && row.subclass !== true)
    assert.equal(serializes(kind.alias()), row.serializes, 'serialize alias')
}

/** Compares copy prototypes in every function with Lean's `CopyPrototype.adopt`, and what
 * `serialize` accepts with `CopyPrototype.serializes`. */
export async function checkCopyPrototypeRuntime(oracle: Oracle): Promise<void> {
  // Ten kinds, each as its own instance and as a subclass instance, and each typed kind given the
  // other's prototype; Temporal is optional.
  const rows = await oracleCorpus(oracle, 'CopyPrototype', 22, 64 * 1024)
  let checked = 0
  for (const line of rows) {
    const row = jsonObject(JSON.parse(line))
    const kind = kinds[integerIn(row.kind, 0, 9)]
    if (kind === undefined) continue
    const source = sourceOf(kind, row)
    for (const [name, original, copy] of copies(kind, source)) {
      assert.notEqual(copy, original, `${name} copies`)
      assert.equal(
        Object.getPrototypeOf(copy) === Object.getPrototypeOf(original),
        row.keeps,
        `${name} prototype`,
      )
      checked += 1
    }
    checkSerializes(kind, row, source)
  }
  console.log(
    `Copy-prototype Lean/native bridge: ${checked} copies by snapshot, reconcile and produce ` +
      'keep their source prototype, subclasses included; serialize accepts only the standard ' +
      'prototype of the kind a value holds',
  )
}
