import assert from 'node:assert/strict'
import { integerIn, jsonObject, oracleCorpus, type Oracle } from './lean-oracle'
import { prototypeHolding } from './property-bridge-fixtures'
import { isReconcileError } from '../src/error'
import { reconcile } from '../src/reconcile'

interface Calls {
  inheritedSetter: number
  ownSetter: number
}

type Row = Record<string, unknown>

/** An accessor whose setter stores what it receives and counts its calls. */
function accessor(
  initial: unknown,
  withSetter: boolean,
  count: () => void,
): Pick<PropertyDescriptor, 'get' | 'set'> {
  let stored = initial
  const set = (value: unknown) => {
    count()
    stored = value
  }
  return { set: withSetter ? set : undefined, get: () => stored }
}

const inheritedDescriptors: Partial<
  Record<string, (calls: Calls) => PropertyDescriptor | undefined>
> = {
  accessor: (calls) => ({
    configurable: true,
    ...accessor(7, true, () => (calls.inheritedSetter += 1)),
  }),
  data: () => ({ configurable: true, value: 7, writable: true }),
  getter: (calls) => ({
    configurable: true,
    ...accessor(7, false, () => (calls.inheritedSetter += 1)),
  }),
  none: () => undefined,
  readonly: () => ({ configurable: true, value: 7, writable: false }),
}

/** Defines the own descriptor a Lean slot describes. */
function defineOwn(target: object, key: string, own: Row, calls: Calls): void {
  const attributes = {
    configurable: own.configurable === true,
    enumerable: own.enumerable === true,
  }
  const value = own.kind === 'none' ? undefined : integerIn(own.value, 0, 1)
  if (own.kind === 'data')
    Object.defineProperty(target, key, { ...attributes, value, writable: own.writable === true })
  else if (own.kind === 'accessor')
    Object.defineProperty(target, key, {
      ...attributes,
      ...accessor(value, own.setter === true, () => (calls.ownSetter += 1)),
    })
  else assert.equal(own.kind, 'none')
}

const KEY = 'reconcileBridgeKey'

/** Builds the native object a Lean slot describes, its inherited descriptor on a fixture
 * prototype or, with `onObject`, on `Object.prototype` itself, which the caller then holds.
 * `__proto__` runs against `Object.prototype`'s own accessor. */
function build(row: Row, onObject: boolean) {
  const calls: Calls = { inheritedSetter: 0, ownSetter: 0 }
  const key = keyOf(row)
  const target = row.proto === true || onObject ? {} : onFixture(row, key, calls)
  defineOwn(target, key, jsonObject(row.own), calls)
  if (row.extensible !== true) Object.preventExtensions(target)
  return { calls, key, target }
}

/** `__proto__`, or the key no other code reads. */
const keyOf = (row: Row): string => (row.proto === true ? '__proto__' : KEY)

/** A new object on a fixture prototype holding the row's inherited descriptor. */
const onFixture = (row: Row, key: string, calls: Calls): object =>
  Object.create(prototypeHolding(inheritedDescriptors, row.inherited, key, calls)) as object

/** Runs `run` while `Object.prototype` holds the row's inherited descriptor for the bridge key,
 * which no other code reads. */
function holdingObjectPrototype<T>(row: Row, calls: Calls, run: () => T): T {
  const descriptor = inheritedDescriptors[String(row.inherited)]?.(calls)
  if (descriptor === undefined) return run()
  // eslint-disable-next-line no-extend-native -- the bridge installs a modified Object.prototype on purpose
  Object.defineProperty(Object.prototype, KEY, descriptor)
  try {
    return run()
  } finally {
    Reflect.deleteProperty(Object.prototype, KEY)
  }
}

/** Describes an own property the way the oracle encodes it. */
function describe(target: object, key: string): Row {
  const descriptor = Object.getOwnPropertyDescriptor(target, key)
  if (descriptor === undefined) return { kind: 'none' }
  const common = {
    configurable: descriptor.configurable === true,
    enumerable: descriptor.enumerable === true,
  }
  if ('value' in descriptor)
    return {
      ...common,
      kind: 'data',
      value: descriptor.value,
      writable: descriptor.writable === true,
    }
  return {
    ...common,
    kind: 'accessor',
    setter: descriptor.set !== undefined,
    value: descriptor.get!(),
  }
}

function expected(descriptor: Row): Row {
  const { configurable, enumerable, kind, setter, value, writable } = descriptor
  if (kind === 'none') return { kind }
  return kind === 'data'
    ? { configurable, enumerable, kind, value, writable }
    : { configurable, enumerable, kind, setter, value }
}

/** Runs `reconcile` and reduces its outcome to `done` or `rejected`. */
function outcome(current: object, next: object): string {
  try {
    assert.equal(reconcile(current, next), current)
    return 'done'
  } catch (error) {
    assert.ok(isReconcileError(error) && error.cause.type === 'PublicationRejected', String(error))
    return 'rejected'
  }
}

type Wrap = (target: object) => object | undefined

/** The ordinary object and a forwarding proxy. */
const wraps: readonly Wrap[] = [(target) => target, (target) => new Proxy(target, {})]

/** Runs `reconcile` on one realization and compares it with the Lean outcome. */
function checkRealization(row: Row, wrap: Wrap, onObject = false): boolean {
  const { calls, key, target } = build(row, onObject)
  if (onObject)
    return holdingObjectPrototype(row, calls, () => compare(row, wrap, calls, key, target, true))
  return compare(row, wrap, calls, key, target)
}

function compare(
  row: Row,
  wrap: Wrap,
  calls: Calls,
  key: string,
  target: object,
  onObject = false,
): boolean {
  const current = wrap(target)
  if (current === undefined) return false
  const before = describe(target, key)
  const next = Object.defineProperty({}, key, {
    configurable: true,
    enumerable: true,
    value: integerIn(row.value, 0, 1),
    writable: true,
  })
  const status = outcome(current, next)
  const after = describe(current, key)
  checkStatus(row, key, status, before, after)
  assert.deepEqual(after, expected(jsonObject(row.after)), `${key}: descriptor`)
  assert.equal(calls.ownSetter, integerIn(row.ownSetterCalls, 0, 1), `${key}: own setter`)
  assert.equal(
    calls.inheritedSetter,
    integerIn(row.inheritedSetterCalls, 0, 0),
    `${key}: inherited`,
  )
  // Object.prototype's own __proto__ setter would replace the prototype.
  assert.equal(Object.getPrototypeOf(current) === Object.prototype, key === '__proto__' || onObject)
  return true
}

/** A rejection before writing leaves the descriptor as it was. */
function checkStatus(row: Row, key: string, status: string, before: Row, after: Row): void {
  const rejectedBefore = row.status === 'rejectedBeforeWriting'
  assert.equal(status, rejectedBefore ? 'rejected' : row.status, `${key}: status`)
  if (rejectedBefore) assert.deepEqual(after, before, `${key}: written before rejection`)
}

const differs = (row: Row): boolean =>
  row.previousStatus !== row.status ||
  JSON.stringify(row.previousAfter) !== JSON.stringify(row.after)

/** Compares `reconcile` on single-key objects with every Lean outcome, natively and through
 * proxies, and counts the outcomes that differ from the previous decision. */
export async function checkPropertyWriteRuntime(oracle: Oracle): Promise<void> {
  // 33 own descriptors × 5 inherited × 2 extensibility × 2 values, and 4 `__proto__` cases.
  const rows = (await oracleCorpus(oracle, 'PropertyWrite', 664, 1024 * 1024)).map((line) =>
    jsonObject(JSON.parse(line)),
  )
  const realizations = rows.flatMap((row) => wraps.filter((wrap) => checkRealization(row, wrap)))
  // The same slots with the inherited descriptor on Object.prototype, as any code can add it.
  const onObject = rows
    .filter((row) => row.proto !== true)
    .flatMap((row) => wraps.filter((wrap) => checkRealization(row, wrap, true)))
  console.log(
    `Property-write Lean/native bridge: ${rows.length} outcomes, ${realizations.length} native ` +
      `realizations through reconcile and ${onObject.length} with the inherited descriptor on ` +
      `Object.prototype; ${rows.filter(differs).length} outcomes differ from the previous decision`,
  )
}
