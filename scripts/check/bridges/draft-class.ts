import assert from 'node:assert/strict'
import { integerIn, jsonObject, oracleCorpus, type Oracle } from '../oracle'
import { produce } from '../../../src/produce'

/** Subclasses that add `custom` and override `has`, as `DraftClassOracle` models them. */
class SubMap extends Map<unknown, unknown> {
  custom(): number {
    return this.size
  }
  override has(key: unknown): boolean {
    return super.has(key)
  }
}

class SubSet extends Set<unknown> {
  custom(): number {
    return this.size
  }
  override has(value: unknown): boolean {
    return super.has(value)
  }
}

/** `DraftClassOracle` prototype identifiers; any other prototype is the draft layer, `9`. */
const prototypes: readonly object[] = [
  Object.prototype,
  Map.prototype,
  Set.prototype,
  SubMap.prototype,
  SubSet.prototype,
]

const names: Readonly<Record<string, PropertyKey>> = {
  iterator: Symbol.iterator,
  toStringTag: Symbol.toStringTag,
}

/** The identifier of the prototype that defines `key` on the value's chain. */
function owner(value: object, key: PropertyKey): number | null {
  for (
    let prototype = Object.getPrototypeOf(value) as object | null;
    prototype !== null;
    prototype = Object.getPrototypeOf(prototype) as object | null
  )
    if (Object.prototype.hasOwnProperty.call(prototype, key)) {
      const index = prototypes.indexOf(prototype)
      return index === -1 ? 9 : index
    }
  return null
}

/** Reads one draft of a `Map` or `Set`, built-in or subclass instance, inside a recipe. */
function withDraft(map: boolean, subclass: boolean, read: (draft: object) => void): void {
  const value: object = map
    ? subclass
      ? new SubMap([['a', 1]])
      : new Map([['a', 1]])
    : subclass
      ? new SubSet(['a'])
      : new Set(['a'])
  produce({ value }, (draft) => {
    read(draft.value)
    return draft
  })
}

/** Checks one `DraftClassOracle` row on a draft: an `instanceof` result or a name's owner. */
function checkRow(row: Record<string, unknown>, draft: object): void {
  if ('isInstance' in row) {
    const prototype = prototypes[integerIn(row.proto, 0, prototypes.length - 1)]
    const constructor = (prototype as { constructor: abstract new () => unknown }).constructor
    assert.equal(draft instanceof constructor, row.isInstance, `instanceof ${JSON.stringify(row)}`)
  } else {
    const name = String(row.name)
    assert.equal(owner(draft, names[name] ?? name), row.owner, `owner ${JSON.stringify(row)}`)
  }
}

/** Compares draft method resolution and `instanceof` with Lean's `DraftClass`. */
export async function checkDraftClassRuntime(oracle: Oracle): Promise<void> {
  // A Map and a Set, as built-in and subclass instances: 13 or 19 names, then 5 prototypes.
  const rows = await oracleCorpus(oracle, 'DraftClass', 84, 64 * 1024)
  for (const line of rows) {
    const row = jsonObject(JSON.parse(line))
    withDraft(row.map === true, row.subclass === true, (draft) => checkRow(row, draft))
  }
  const instances = rows.filter((line) => line.includes('"isInstance"')).length
  // A subclass method runs on the draft and reads it through the draft's own methods.
  const value = new SubMap([['a', 1]])
  const result = produce({ value }, (draft) => {
    draft.value.set('b', 2)
    assert.equal(draft.value.custom(), 2)
    assert.equal(Object.prototype.toString.call(draft.value), '[object Map]')
    assert.equal(draft.value.constructor, SubMap)
    return draft
  })
  assert.ok(result.value instanceof SubMap)
  console.log(
    `Draft-class Lean/native bridge: ${rows.length - instances} names resolve on Map and Set ` +
      `drafts where Lean resolves them, and ${instances} instanceof checks agree`,
  )
}
