import assert from 'node:assert/strict'
import { jsonObject, oracleCorpus, type Oracle } from './lean-oracle'
import { decodeKey } from './property-bridge-fixtures'
import { isReconcileError } from '../src/error'
import { reconcile } from '../src/reconcile'

const symbols = [Symbol('first'), Symbol('second')]

/** Decodes a Lean key code; labels run to 2: three names, two symbols and one integer key. */
function key(code: unknown): PropertyKey {
  return decodeKey(code, 8, symbols)
}

function keys(value: unknown): PropertyKey[] {
  assert.ok(Array.isArray(value))
  return value.map(key)
}

/** A current object in the given own-key order; fixed keys are accessors that store values. */
function build(order: readonly PropertyKey[], fixed: ReadonlySet<PropertyKey>) {
  const target: Record<PropertyKey, unknown> = {}
  const calls = { setter: 0 }
  for (const property of order) {
    if (fixed.has(property)) storingAccessor(target, property, calls)
    else target[property] = 0
  }
  return { calls, target }
}

function storingAccessor(target: object, property: PropertyKey, calls: { setter: number }): void {
  let stored: unknown = 0
  Object.defineProperty(target, property, {
    configurable: true,
    enumerable: true,
    get: () => stored,
    set: (value: unknown) => {
      calls.setter += 1
      stored = value
    },
  })
}

function snapshotOf(target: object): Array<[PropertyKey, unknown]> {
  return Reflect.ownKeys(target).map((property) => [property, Reflect.get(target, property)])
}

function attempt(current: object, next: object): boolean {
  try {
    assert.equal(reconcile(current, next), current)
    return true
  } catch (error) {
    assert.ok(isReconcileError(error) && error.cause.type === 'PublicationRejected', String(error))
    return false
  }
}

/** Runs `reconcile` for one fixed set and compares it with Lean's kept keys. */
function checkFixed(
  current: readonly PropertyKey[],
  desired: readonly PropertyKey[],
  kept: ReadonlySet<PropertyKey>,
  fixed: ReadonlySet<PropertyKey>,
): boolean {
  const { calls, target } = build(current, fixed)
  const before = snapshotOf(target)
  const next = Object.fromEntries(desired.map((property) => [property, 1]))
  const placeable = [...fixed].every((property) => kept.has(property))
  assert.equal(attempt(target, next), placeable, 'placement outcome')
  if (placeable) {
    assert.deepEqual(Reflect.ownKeys(target), desired, 'placed order')
    assert.ok(desired.every((property) => Reflect.get(target, property) === 1))
    for (const property of fixed)
      assert.equal(typeof Object.getOwnPropertyDescriptor(target, property)?.get, 'function')
  } else {
    assert.deepEqual(snapshotOf(target), before, 'written before rejection')
    assert.equal(calls.setter, 0, 'setter before rejection')
  }
  return placeable
}

/** Every subset of the keys both orders share, as candidate fixed sets. */
function subsets(shared: readonly PropertyKey[]): Array<Set<PropertyKey>> {
  return Array.from(
    { length: 2 ** shared.length },
    (_, mask) => new Set(shared.filter((_property, index) => ((mask >> index) & 1) === 1)),
  )
}

/** Compares `reconcile` with Lean's greedy placement for every pair of own-key orders and every
 * set of accessors both orders share: it succeeds with the desired order exactly when Lean keeps
 * every accessor, and otherwise writes nothing. */
export async function checkPropertyPlacementRuntime(oracle: Oracle): Promise<void> {
  // 160 own-key orders: an optional integer key, up to three names and up to two symbols.
  const rows = await oracleCorpus(oracle, 'PropertyPlacement', 25_600, 8 * 1024 * 1024)
  let cases = 0
  let rejected = 0
  for (const line of rows) {
    const row = jsonObject(JSON.parse(line))
    const current = keys(row.current)
    const desired = keys(row.desired)
    const kept = new Set(keys(row.kept))
    const shared = current.filter((property) => desired.includes(property))
    for (const fixed of subsets(shared)) {
      cases += 1
      if (!checkFixed(current, desired, kept, fixed)) rejected += 1
    }
  }
  console.log(
    `Property-placement Lean/native bridge: ${rows.length} order pairs, ${cases} accessor sets, ` +
      `${rejected} rejected exactly where Lean keeps no placement`,
  )
}
