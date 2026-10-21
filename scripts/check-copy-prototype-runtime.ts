import assert from 'node:assert/strict'
import { integerIn, jsonObject, oracleCorpus, type Oracle } from './lean-oracle'
import { produce } from '../src/produce'
import { reconcile } from '../src/reconcile'
import { snapshot } from '../src/snapshot'
import { deserialize } from '../src/deserialize'
import { serialize } from '../src/serialize'

interface Kind {
  readonly change: (value: never) => void
  readonly make: (subclass: boolean) => object
}

class DataViewSubclass extends DataView<ArrayBuffer> {}

const kinds: readonly Kind[] = [
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
]

/** The copies each function builds of one value: a snapshot, an object reconcile adds and a
 * produce result the recipe changed. */
function copies(kind: Kind, subclass: boolean): Array<[string, object, object]> {
  const source = (): object => kind.make(subclass)
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

/** Compares copy prototypes in every function with Lean's `CopyPrototype.adopt`, and what
 * `serialize` accepts with `CopyPrototype.serializes`. */
export async function checkCopyPrototypeRuntime(oracle: Oracle): Promise<void> {
  // Eight kinds, each as its own instance and as a subclass instance; Temporal is optional.
  const rows = await oracleCorpus(oracle, 'CopyPrototype', 16, 64 * 1024)
  let checked = 0
  for (const line of rows) {
    const row = jsonObject(JSON.parse(line))
    const kind = kinds[integerIn(row.kind, 0, 7)]
    if (kind === undefined) continue
    for (const [name, source, copy] of copies(kind, row.subclass === true)) {
      assert.notEqual(copy, source, `${name} copies`)
      assert.equal(
        Object.getPrototypeOf(copy) === Object.getPrototypeOf(source),
        row.keeps,
        `${name} prototype`,
      )
      checked += 1
    }
    assert.equal(serializes(kind.make(row.subclass === true)), row.serializes, 'serialize')
  }
  console.log(
    `Copy-prototype Lean/native bridge: ${checked} copies by snapshot, reconcile and produce ` +
      'keep their source prototype, subclasses included; serialize accepts only standard prototypes',
  )
}
