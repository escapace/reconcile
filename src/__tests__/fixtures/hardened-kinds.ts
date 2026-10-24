// Child-process driver for standard-prototypes.spec.ts: every function on every value kind, run
// once in an ordinary runtime and once in each hardened one, where a standard prototype's methods
// may be accessors and every intrinsic may be frozen. The spec compares the outcomes, which must be
// equal and must not throw. Freezing protects properties, not the contents a built-in keeps in
// internal slots, so `reconcile` updates a frozen `Map`, `Set`, `Date`, buffer, view or URL in
// place, and `produce` changes a copy of it.
import { deserialize, produce, reconcile, serialize, snapshot } from '../../index'

class Bytes extends Uint8Array {}
class Members extends Set<unknown> {}
class Moment extends Date {}
class Point {
  x = 1
}
class Tally extends Map<unknown, unknown> {}

/** A kind: how to build a fresh value, how a recipe changes it, whether `serialize` takes it and
 * whether a frozen value of it can change, its contents being in internal slots. */
interface Kind {
  readonly serializable: boolean
  readonly frozen?: boolean
  readonly change: (value: never) => void
  readonly make: () => unknown
}

const kept = (): void => undefined

const first = (value: Uint8Array | unknown[]): void => {
  value[0] = 9
}

const kinds: Record<string, Kind> = {
  array: { change: first, serializable: true, make: () => [1, { a: 1 }, [2]] },
  bigint: {
    serializable: true,
    change: (value: BigInt64Array) => {
      value[0] = 9n
    },
    make: () => new BigInt64Array([1n, -2n]),
  },
  buffer: {
    frozen: true,
    serializable: true,
    change: (value: ArrayBuffer) => first(new Uint8Array(value)),
    make: () => new Uint8Array([1, 2, 3]).buffer,
  },
  date: {
    frozen: true,
    serializable: true,
    change: (value: Date) => value.setTime(9),
    make: () => new Date(5),
  },
  dateSubclass: {
    frozen: true,
    serializable: false,
    change: (value: Date) => value.setTime(9),
    make: () => new Moment(6),
  },
  float: { change: first, serializable: true, make: () => new Float64Array([1.5, -0]) },
  function: { change: kept, serializable: false, make: () => kept },
  instance: {
    serializable: false,
    change: (value: Point) => {
      value.x = 2
    },
    make: () => new Point(),
  },
  map: {
    frozen: true,
    serializable: true,
    change: (value: Map<unknown, unknown>) => value.set('z', 2),
    make: () => new Map<unknown, unknown>([['a', { n: 1 }]]),
  },
  mapSubclass: {
    frozen: true,
    serializable: false,
    change: (value: Map<unknown, unknown>) => value.set('z', 2),
    make: () => new Tally([['a', 1]]),
  },
  nullPrototype: {
    serializable: true,
    change: (value: Record<string, unknown>) => {
      value.a = 2
    },
    make: () => Object.assign(Object.create(null) as object, { a: 1, b: [1] }),
  },
  parameters: {
    frozen: true,
    serializable: true,
    change: (value: URLSearchParams) => value.append('c', '3'),
    make: () => new URLSearchParams('a=1&b=2'),
  },
  plain: {
    serializable: true,
    change: (value: Record<string, unknown>) => {
      value.a = 2
    },
    make: () => ({ a: 1, b: { c: [1] } }),
  },
  set: {
    frozen: true,
    serializable: true,
    change: (value: Set<unknown>) => value.add('z'),
    make: () => new Set<unknown>([{ m: 1 }, 1]),
  },
  setSubclass: {
    frozen: true,
    serializable: false,
    change: (value: Set<unknown>) => value.add('z'),
    make: () => new Members([1, 2]),
  },
  // eslint-disable-next-line no-sparse-arrays -- a hole is a case
  sparse: { change: first, serializable: true, make: () => [1, , 3] },
  symbolKey: {
    serializable: false,
    change: (value: Record<PropertyKey, unknown>) => {
      value[Symbol.for('k')] = 2
    },
    make: () => ({ a: 1, [Symbol.for('k')]: 1 }),
  },
  url: {
    frozen: true,
    serializable: true,
    change: (value: URL) => {
      value.search = '?y=2'
    },
    make: () => new URL('https://a.test/p?x=1'),
  },
  view: {
    frozen: true,
    serializable: true,
    change: (value: DataView) => value.setUint8(0, 9),
    make: () => new DataView(new Uint8Array([7, 8, 9]).buffer, 1, 2),
  },
  viewSubclass: { change: first, serializable: false, make: () => new Bytes([4, 5]) },
}

const bytesOf = (value: ArrayBuffer | ArrayBufferView): string =>
  (ArrayBuffer.isView(value)
    ? new Uint8Array(value.buffer, value.byteOffset, value.byteLength)
    : new Uint8Array(value)
  ).join(',')

type Describe = (value: unknown, seen: Map<object, number>) => string

/** How each built-in kind is described; ordinary objects list their own keys. */
const renderers: Array<
  [
    (value: object) => boolean,
    (value: never, describe: Describe, seen: Map<object, number>) => string,
  ]
> = [
  [
    (value) => value instanceof Map,
    (value: Map<unknown, unknown>, describe, seen) =>
      [...Map.prototype.entries.call(value)]
        .map(([key, entry]) => `${describe(key, seen)}=>${describe(entry, seen)}`)
        .join(','),
  ],
  [
    (value) => value instanceof Set,
    (value: Set<unknown>, describe, seen) =>
      [...Set.prototype.values.call(value)].map((member) => describe(member, seen)).join(','),
  ],
  [(value) => value instanceof Date, (value: Date) => String(Date.prototype.getTime.call(value))],
  [(value) => value instanceof ArrayBuffer || ArrayBuffer.isView(value), bytesOf],
  [(value) => value instanceof URL, (value: URL) => value.href],
  [(value) => value instanceof URLSearchParams, (value: URLSearchParams) => value.toString()],
]

const primitive = (value: unknown): string =>
  Object.is(value, -0) ? '-0' : `${typeof value}:${String(value)}`

const className = (value: object): string =>
  (Object.getPrototypeOf(value) as { constructor?: { name?: string } } | null)?.constructor?.name ??
  'null'

const fields = (value: object, seen: Map<object, number>): string =>
  Reflect.ownKeys(value)
    .filter((key) => key !== 'length' || !Array.isArray(value))
    .map((key) => `${String(key)}:${describe((value as Record<PropertyKey, unknown>)[key], seen)}`)
    .join(',')

/** A canonical description that does not depend on the runtime's hardening. */
const describe: Describe = (value, seen) => {
  if (typeof value !== 'object' || value === null) return primitive(value)
  if (seen.has(value)) return `#${seen.get(value)}`
  seen.set(value, seen.size)
  const renderer = renderers.find(([test]) => test(value))
  return renderer === undefined
    ? `${className(value)}{${fields(value, seen)}}`
    : `${className(value)}(${renderer[1](value as never, describe, seen)})`
}

/** Runs every case; a hardened runtime may lock down after this module loads and before it runs. */
export function run(): { cases: number; failures: string[]; outcomes: string[] } {
  const outcomes: string[] = []
  const failures: string[] = []
  const attempt = (label: string, operation: () => unknown): void => {
    let outcome: string
    try {
      outcome = `${label}: ${describe(operation(), new Map())}`
    } catch (error) {
      outcome = `${label}: throws ${error instanceof Error ? `${error.name} ${error.message}` : String(error)}`
      failures.push(outcome)
    }
    outcomes.push(outcome)
  }
  for (const [name, { change, frozen, make, serializable }] of Object.entries(kinds)) {
    const changed = (value = make()) =>
      produce({ value }, (draft) => {
        change(draft.value as never)
        return draft
      })
    attempt(`${name} snapshot`, () => snapshot({ value: make() }))
    if (serializable)
      attempt(`${name} serialize`, () =>
        deserialize(JSON.parse(JSON.stringify(serialize({ value: make() }))), { maxBytes: 1e5 }),
      )
    attempt(`${name} reconcile adds`, () => reconcile({}, { value: make() }))
    attempt(`${name} reconcile updates`, () => reconcile({ value: make() }, changed()))
    attempt(`${name} produce`, changed)
    attempt(`${name} produce unchanged`, () => {
      const current = { value: make() }
      return produce(current, (draft) => draft) === current
    })
    if (frozen !== true) continue
    attempt(`${name} reconcile updates frozen`, () => {
      const value = Object.freeze(make())
      const current = Object.freeze({ value })
      return [reconcile(current, changed()) === current, current.value === value, value]
    })
    attempt(`${name} produce changes a copy of frozen`, () => {
      const value = Object.freeze(make())
      const result = changed(value)
      return [result.value === value, Object.isFrozen(result.value), value, result.value]
    })
  }
  return { cases: outcomes.length, failures, outcomes }
}
