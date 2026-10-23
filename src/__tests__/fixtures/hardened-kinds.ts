// Child-process driver for standard-prototypes.spec.ts: every function on every value kind, run
// once in an ordinary runtime and once in each hardened one, where a standard prototype's methods
// may be accessors. The spec compares the outcomes, which must be equal and must not throw.
import { deserialize, produce, reconcile, serialize, snapshot } from '../../index'

class Bytes extends Uint8Array {}
class Members extends Set<unknown> {}
class Moment extends Date {}
class Point {
  x = 1
}
class Tally extends Map<unknown, unknown> {}

/** A kind: how to build a fresh value, how a recipe changes it, and whether `serialize` takes it. */
interface Kind {
  readonly serializable: boolean
  readonly change: (value: never) => void
  readonly make: () => unknown
}

const first = (value: Uint8Array | unknown[]): void => {
  value[0] = 9
}

const kinds: Record<string, Kind> = {
  array: { change: first, serializable: true, make: () => [1, { a: 1 }, [2]] },
  buffer: {
    serializable: true,
    change: (value: ArrayBuffer) => first(new Uint8Array(value)),
    make: () => new Uint8Array([1, 2, 3]).buffer,
  },
  date: { serializable: true, change: (value: Date) => value.setTime(9), make: () => new Date(5) },
  dateSubclass: {
    serializable: false,
    change: (value: Date) => value.setTime(9),
    make: () => new Moment(6),
  },
  float: { change: first, serializable: true, make: () => new Float64Array([1.5, -0]) },
  instance: {
    serializable: false,
    change: (value: Point) => {
      value.x = 2
    },
    make: () => new Point(),
  },
  map: {
    serializable: true,
    change: (value: Map<unknown, unknown>) => value.set('z', 2),
    make: () => new Map<unknown, unknown>([['a', { n: 1 }]]),
  },
  mapSubclass: {
    serializable: false,
    change: (value: Map<unknown, unknown>) => value.set('z', 2),
    make: () => new Tally([['a', 1]]),
  },
  parameters: {
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
    serializable: true,
    change: (value: Set<unknown>) => value.add('z'),
    make: () => new Set<unknown>([{ m: 1 }, 1]),
  },
  setSubclass: {
    serializable: false,
    change: (value: Set<unknown>) => value.add('z'),
    make: () => new Members([1, 2]),
  },
  // eslint-disable-next-line no-sparse-arrays -- a hole is a case
  sparse: { change: first, serializable: true, make: () => [1, , 3] },
  url: {
    serializable: true,
    change: (value: URL) => {
      value.search = '?y=2'
    },
    make: () => new URL('https://a.test/p?x=1'),
  },
  view: {
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

const outcomes: string[] = []
const failures: string[] = []
const run = (label: string, operation: () => unknown): void => {
  let outcome: string
  try {
    outcome = `${label}: ${describe(operation(), new Map())}`
  } catch (error) {
    outcome = `${label}: throws ${error instanceof Error ? `${error.name} ${error.message}` : String(error)}`
    failures.push(outcome)
  }
  outcomes.push(outcome)
}

for (const [name, { change, make, serializable }] of Object.entries(kinds)) {
  const changed = () =>
    produce({ value: make() }, (draft) => {
      change(draft.value as never)
      return draft
    })
  run(`${name} snapshot`, () => snapshot({ value: make() }))
  if (serializable)
    run(`${name} serialize`, () =>
      deserialize(JSON.parse(JSON.stringify(serialize({ value: make() }))), { maxBytes: 1e5 }),
    )
  run(`${name} reconcile adds`, () => reconcile({}, { value: make() }))
  run(`${name} reconcile updates`, () => reconcile({ value: make() }, changed()))
  run(`${name} produce`, changed)
  run(`${name} produce unchanged`, () => {
    const current = { value: make() }
    return produce(current, (draft) => draft) === current
  })
}

export const result = { cases: outcomes.length, failures, outcomes }
