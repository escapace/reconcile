import assert from 'node:assert/strict'
import { integerIn, jsonObject, oracleCorpus, type Oracle } from './lean-oracle'
import { prototypeHolding } from './property-bridge-fixtures'
import { deserialize } from '../src/deserialize'
import { produce } from '../src/produce'
import { reconcile } from '../src/reconcile'
import { serialize } from '../src/serialize'
import { snapshot } from '../src/snapshot'

type Row = Record<string, unknown>

interface Calls {
  setter: number
}

const inheritedDescriptors: Partial<
  Record<string, (calls: Calls) => PropertyDescriptor | undefined>
> = {
  accessor: (calls) => ({
    configurable: true,
    get: () => 7,
    set: () => {
      calls.setter += 1
    },
  }),
  data: () => ({ configurable: true, value: 7, writable: true }),
  getter: () => ({ configurable: true, get: () => 7 }),
  none: () => undefined,
  readonly: () => ({ configurable: true, value: 7, writable: false }),
}

/** The source whose own data property a new object must copy, with the row's enumerability, on
 * a custom prototype holding the inherited descriptor, a null prototype or `Object.prototype`. */
function sourceOf(row: Row, key: string, calls: Calls): object {
  const prototype =
    row.base === 'custom'
      ? prototypeHolding(inheritedDescriptors, row.inherited, key, calls)
      : row.base === 'null'
        ? null
        : Object.prototype
  return Object.defineProperty(Object.create(prototype) as object, key, {
    configurable: true,
    enumerable: row.enumerable === true,
    value: integerIn(row.value, 0, 1),
    writable: true,
  })
}

/** Runs `run` while `Object.prototype` holds the row's descriptor for `key`, which no other code
 * reads; `__proto__` is its own accessor. */
function holdingObjectPrototype<T>(row: Row, key: string, calls: Calls, run: () => T): T {
  const make = inheritedDescriptors[String(row.inherited)]
  assert.ok(make !== undefined, `Unknown inherited descriptor ${String(row.inherited)}`)
  const descriptor = row.base === 'object' && row.proto !== true ? make(calls) : undefined
  if (descriptor === undefined) return run()
  // eslint-disable-next-line no-extend-native -- the bridge installs a modified Object.prototype on purpose
  Object.defineProperty(Object.prototype, key, descriptor)
  try {
    return run()
  } finally {
    Reflect.deleteProperty(Object.prototype, key)
  }
}

/** Every way the library builds a new object from a source: `snapshot`, a `produce` rebuild, an
 * object `reconcile` adds and, for standard prototypes, `deserialize`, which `serialize` refuses a
 * non-enumerable property. */
function builds(source: object, standard: boolean, enumerable: boolean): object[] {
  const rebuilt = produce(source as Record<string, unknown>, (draft) => {
    draft.other = 1
    return draft
  })
  const holder: Record<string, unknown> = { child: 0 }
  reconcile(holder, { child: source })
  const results = [snapshot(source) as object, rebuilt, holder.child as object]
  if (standard && enumerable)
    results.push(
      deserialize(JSON.parse(JSON.stringify(serialize(source))), { maxBytes: 1024 }) as object,
    )
  else if (standard) assert.throws(() => serialize(source), /non-enumerable/)
  return results
}

/** Compares every new object built from one Lean case with the Lean outcome. */
function checkRow(row: Row): number {
  const key = row.proto === true ? '__proto__' : 'reconcileBridgeKey'
  const calls: Calls = { setter: 0 }
  const after = jsonObject(row.after)
  const results = holdingObjectPrototype(row, key, calls, () =>
    builds(sourceOf(row, key, calls), row.base !== 'custom', row.enumerable === true),
  )
  for (const result of results) {
    assert.equal(row.ok, true)
    assert.deepEqual(Object.getOwnPropertyDescriptor(result, key), {
      configurable: after.configurable,
      enumerable: after.enumerable,
      value: after.value,
      writable: after.writable,
    })
  }
  assert.equal(calls.setter, integerIn(row.setterCalls, 0, 0), 'inherited setter')
  return results.length
}

/** Compares new-object construction in every builder with Lean's `constructFromOn`. */
export async function checkPropertyConstructRuntime(oracle: Oracle): Promise<void> {
  // A custom prototype and Object.prototype holding each of 5 descriptors, a null prototype and
  // `__proto__`, each with 2 values, enumerable or not.
  const rows = await oracleCorpus(oracle, 'PropertyConstructOn', 48, 64 * 1024)
  const realizations = rows.reduce((sum, line) => sum + checkRow(jsonObject(JSON.parse(line))), 0)
  console.log(
    `Property-construct Lean/native bridge: ${rows.length} outcomes, ${realizations} new objects ` +
      'built by snapshot, produce, reconcile and deserialize, Object.prototype modified or not',
  )
}
