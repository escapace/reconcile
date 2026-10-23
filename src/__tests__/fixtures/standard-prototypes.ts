/* eslint-disable typescript/no-explicit-any, typescript/no-unsafe-assignment, typescript/no-unsafe-call, typescript/no-unsafe-member-access, typescript/no-unsafe-return -- recipes write through untyped drafts. */
// Child-process driver for standard-prototypes.spec.ts: it adds properties to Object.prototype and
// Array.prototype, which would disturb the test runner in its own process. The spec bundles it
// without helpers, imports it in a child process and reads `result` from standard output.
import constants from '../../../scripts/constants.json' with { type: 'json' }
import { deserialize, produce, reconcile, requiredMaxBytes, serialize, snapshot } from '../../index'

// Names the library read or wrote through a standard prototype before it detached its internal
// objects, with the descriptor, iterator and thenable protocol names. Data keys below are
// non-ASCII so they never collide with these.
const NAMES = [
  'accessorObservations',
  'base',
  'beginCallback',
  'callerMemo',
  'carrier',
  'cause',
  'configurable',
  'constructed',
  'context',
  'copy',
  'copyPrototype',
  'count',
  'currentReference',
  'dependencyEquivalent',
  'desired',
  'detail',
  'done',
  'edgeCallback',
  'enumerable',
  'facts',
  'fill',
  'finalization',
  'forcedOwnedCopies',
  'get',
  'handle',
  'implications',
  'keys',
  'kind',
  'kinds',
  'layout',
  'link',
  'marks',
  'memoKey',
  'methods',
  'names',
  'nativeOwners',
  'next',
  'node',
  'observed',
  'payload',
  'phase',
  'pinned',
  'plan',
  'properties',
  'provided',
  'record',
  'references',
  'return',
  'rules',
  'session',
  'set',
  'slots',
  'specialCloneBaseToClone',
  'specialCloneCloneToBase',
  'state',
  'statesByIdentity',
  'storage',
  'target',
  'Temporal',
  'then',
  'throw',
  'types',
  'untrackedSpecialsToClone',
  'value',
  'values',
  'writable',
  'write',
]
// Every internal member name the published bundle renames is probed as well, so a new internal
// field is covered without being listed here.
const PROBED = [
  ...new Set([...NAMES, ...Object.values(constants.builds).flatMap((build) => build.mangle)]),
]
// Index accessors are left out: an accessor at an index of Array.prototype or Object.prototype
// runs inside native push and changes the data itself.
const INDICES = Array.from({ length: 32 }, (_, index) => String(index))
// Read-only properties named like a field the library sets on its own objects, functions named
// like a native method an engine may lack, and well-known symbols that native operations read.
const READ_ONLY = ['cause', 'nativeOwners']
const FUNCTIONS = ['fromBase64', 'toBase64']
// Symbol.toPrimitive is left out: Node's own URL code converts objects to strings.
const SYMBOLS = [Symbol.isConcatSpreadable, Symbol.species, Symbol.toStringTag]

const ignore = (): undefined => undefined
/** A property descriptor that inherits nothing, so the definition reads only its own fields. */
const bare = (descriptor: PropertyDescriptor): PropertyDescriptor =>
  Object.setPrototypeOf(descriptor, null)
const hasOwn = Object.hasOwn
const ownKeys = Reflect.ownKeys
const describe = Object.getOwnPropertyDescriptor
const getPrototypeOf = Object.getPrototypeOf
const toTag = (value: object): string => Object.prototype.toString.call(value)

const scalar = (value: unknown): string =>
  typeof value === 'bigint'
    ? `${value}n`
    : typeof value === 'string'
      ? JSON.stringify(value)
      : Object.is(value, -0)
        ? '-0'
        : String(value)

function tag(value: object): string {
  const prototype: unknown = getPrototypeOf(value)
  if (prototype === null) return 'null'
  if (prototype === Object.prototype) return 'O'
  return prototype === Array.prototype ? 'A' : toTag(value)
}

/** The internal contents of a built-in value, read through its prototype's own methods. */
function contents(value: object, out: string[], visit: (value: unknown) => void): void {
  if (value instanceof Map)
    Map.prototype.forEach.call(value, (member: unknown, key: unknown) => {
      visit(key)
      out.push('=>')
      visit(member)
    })
  else if (value instanceof Set)
    Set.prototype.forEach.call(value, (member: unknown) => visit(member))
  else if (value instanceof Date) out.push(String(Date.prototype.getTime.call(value)))
  else if (value instanceof URL) out.push(URL.prototype.toString.call(value))
  else if (ArrayBuffer.isView(value))
    out.push(
      Array.prototype.join.call(
        new Uint8Array(value.buffer, value.byteOffset, value.byteLength),
        ',',
      ),
    )
  else if (value instanceof ArrayBuffer)
    out.push(Array.prototype.join.call(new Uint8Array(value), ','))
}

/** A canonical text of a graph that reads no inherited property. */
function canonical(root: unknown): string {
  const seen = new Map<object, number>()
  const out: string[] = []
  const visit = (value: unknown): void => {
    if (typeof value !== 'object' || value === null) {
      out.push(scalar(value))
      return
    }
    const index = seen.get(value)
    if (index !== undefined) {
      out.push(`@${index}`)
      return
    }
    seen.set(value, seen.size)
    out.push(`<${tag(value)}`)
    contents(value, out, visit)
    const keys = ownKeys(value)
    for (let key = 0; key < keys.length; key++) {
      const descriptor = describe(value, keys[key])!
      out.push(` ${String(keys[key])}${descriptor.enumerable === true ? '' : '~'}:`)
      if (hasOwn(descriptor, 'value')) visit(descriptor.value)
      else out.push('accessor')
    }
    out.push('>')
  }
  visit(root)
  return out.join('')
}

const K = (index: number): string => `κ${index}`

/** A `Map` with its own `entries`, which every walk of it calls instead of the built-in one. */
function ownEntries(): Map<unknown, unknown> {
  return Object.defineProperty(
    new Map<unknown, unknown>([[K(55), { [K(56)]: 1 }]]),
    'entries',
    bare({
      configurable: true,
      enumerable: false,
      writable: true,
      value(this: Map<unknown, unknown>) {
        return Map.prototype.entries.call(this)
      },
    }),
  )
}

/** `[1, <hole>, 3, <hole>]`, whose holes an index on a standard prototype must not fill. */
function holey(): unknown[] {
  const array = [1, 2, 3, 4]
  Reflect.deleteProperty(array, 1)
  Reflect.deleteProperty(array, 3)
  return array
}

function plain(): Record<string, unknown> {
  const shared = { [K(1)]: 'σ', [K(2)]: [1, 2, 3] }
  const value: Record<string, unknown> = {
    [K(10)]: new URL('https://e.x/a?b=c'),
    [K(11)]: 10n,
    [K(12)]: [undefined, Number.NaN, -0],
    [K(13)]: Object.assign(Object.create(null) as object, { [K(14)]: 'ν' }),
    [K(23)]: holey(),
    [K(3)]: [shared, shared, { [K(4)]: 1 }],
    [K(5)]: new Map<unknown, unknown>([
      [1, [shared]],
      [K(6), shared],
    ]),
    [K(54)]: ownEntries(),
    [K(7)]: new Set<unknown>([shared, 'τ']),
    [K(8)]: new Date(0),
    [K(9)]: new Uint8Array([1, 2, 3]),
  }
  Object.defineProperty(
    value,
    K(15),
    bare({ configurable: true, enumerable: true, value, writable: true }),
  )
  return value
}

/** A `Map` that walks itself through its own generator, which `for...of` closes natively. */
class Walked extends Map<unknown, unknown> {
  override *[Symbol.iterator](): MapIterator<[unknown, unknown]> {
    yield* Map.prototype.entries.call(this)
  }
}

class Point {
  declare x: number
  constructor(x: number) {
    this.x = x
  }
  get double(): number {
    return this.x * 2
  }
}

function rich(): Record<string, unknown> {
  const buffer = new ArrayBuffer(16)
  const shared = { [K(30)]: 1 }
  const hidden: Record<PropertyKey, unknown> = { [K(31)]: shared }
  const define = (key: string, value: unknown, enumerable: boolean) =>
    Object.defineProperty(
      hidden,
      key,
      bare({ configurable: true, enumerable, value, writable: true }),
    )
  define(K(32), 7, false)
  hidden[Symbol.for('κ')] = 'symbol'
  define('__proto__', { [K(33)]: 1 }, true)
  return {
    [K(35)]: [new Point(1), new Point(2)],
    [K(36)]: hidden,
    [K(37)]: [1, 2, 3, 4, 5, 6, 7, 8, 9, shared],
    [K(38)]: {
      [K(43)]: new Uint8Array(buffer, 0, 4),
      [K(44)]: new DataView(buffer, 4, 8),
      [K(45)]: buffer,
    },
    [K(39)]: {
      get [K(34)]() {
        return 5
      },
    },
    [K(40)]: new Map<unknown, unknown>([[shared, new Set([shared])]]),
    [K(41)]: new URLSearchParams('a=1&b=2'),
    [K(46)]: new Walked([[K(47), { [K(48)]: 1 }]]),
  }
}

const wire = JSON.stringify(serialize(plain()))
const operations: Array<[string, () => unknown]> = [
  ['snapshot', () => snapshot(plain())],
  ['snapshot/rich', () => snapshot(rich())],
  [
    'produce/subclass',
    () =>
      produce(rich(), (draft: any) => {
        draft[K(46)].get(K(47))[K(48)] = 2
      }),
  ],
  [
    'produce/set',
    () =>
      produce(plain(), (draft: any) => {
        draft[K(3)][0][K(1)] = 'ω'
        draft[K(3)][2][K(4)] = 2
      }),
  ],
  [
    'produce/push',
    () =>
      produce(plain(), (draft: any) => {
        draft[K(3)].push({ [K(16)]: 1 })
        draft[K(3)][0][K(2)].push(4)
      }),
  ],
  [
    'produce/collections',
    () =>
      produce(plain(), (draft: any) => {
        draft[K(5)].get(K(6))[K(1)] = 'μ'
        draft[K(5)].set(K(17), 1)
        draft[K(7)].add('υ')
        draft[K(5)].delete(1)
      }),
  ],
  [
    'produce/holes',
    () =>
      produce(plain(), (draft: any) => {
        draft[K(23)][2] = 9
      }),
  ],
  [
    'produce/delete',
    () =>
      produce(plain(), (draft: any) => {
        delete draft[K(11)]
        draft[K(3)].splice(1, 1)
      }),
  ],
  [
    'produce/unchanged',
    () => {
      const current = plain()
      const result: unknown = produce(current, ignore)
      return result === current
    },
  ],
  [
    'produce/iterate',
    () =>
      produce(plain(), (draft: any) => {
        let count = 0
        for (const member of draft[K(3)]) if (member !== undefined) count++
        for (const entry of draft[K(5)]) count += entry.length
        for (const member of draft[K(7)]) if (typeof member === 'string') draft[K(7)].delete(member)
        draft[K(3)].forEach((member: any) => {
          if (typeof member === 'object' && K(4) in member) member[K(4)] = count
        })
      }),
  ],
  [
    'produce/search',
    () =>
      produce(plain(), (draft: any) => {
        const first = draft[K(3)][0]
        draft[K(16)] = [
          draft[K(3)].includes(first),
          draft[K(3)].indexOf(first),
          draft[K(3)].lastIndexOf(first),
        ]
        draft[K(17)] = [...draft[K(7)].union(new Set(['ψ']))]
      }),
  ],
  [
    'produce/rich',
    () =>
      produce(rich(), (draft: any) => {
        draft[K(35)][0].x = 9
        draft[K(36)][K(31)][K(30)] = 2
        draft[K(37)][3] = 'h'
        draft[K(38)][K(43)][0] = 9
        draft[K(40)].forEach((member: any) => member.add(1))
        draft[K(41)].append('c', '3')
      }),
  ],
  [
    'reconcile/update',
    () => {
      const next: any = plain()
      next[K(3)][0][K(1)] = 'ω'
      next[K(3)].push({ [K(18)]: [1] })
      Object.defineProperty(
        next,
        K(19),
        bare({ configurable: true, enumerable: true, value: { [K(20)]: 2 }, writable: true }),
      )
      delete next[K(11)]
      next[K(5)].set(K(21), 3)
      return reconcile(plain(), next)
    },
  ],
  ['reconcile/replace', () => reconcile(plain(), { [K(22)]: [1, { [K(23)]: 2 }] })],
  [
    'reconcile/rich',
    () => {
      const next: any = rich()
      next[K(35)].reverse()
      next[K(36)][K(31)] = { [K(42)]: 1 }
      next[K(37)].splice(3)
      next[K(41)].append('d', '4')
      return reconcile(rich(), next)
    },
  ],
  [
    'reconcile/reorder',
    () =>
      reconcile(
        { [K(50)]: 1, [K(51)]: 2, [K(52)]: { [K(53)]: [1, 2] } },
        { [K(50)]: 3, [K(51)]: 2, [K(52)]: { [K(53)]: [2, 1, 3] } },
      ),
  ],
  ['serialize', () => serialize(plain())],
  [
    'serialize/rich',
    () => {
      const value = rich()
      delete value[K(35)]
      delete value[K(36)]
      delete value[K(39)]
      return serialize(value)
    },
  ],
  [
    'reconcile/url',
    () => reconcile({ [K(24)]: 1 }, { [K(24)]: 1, [K(25)]: new URL('https://e.x/?q=1') }),
  ],
  ['reconcile/rejected', () => reconcile({ [K(26)]: [] }, [])],
  ['deserialize', () => deserialize(JSON.parse(wire), { maxBytes: 1e6 })],
  ['requiredMaxBytes', () => requiredMaxBytes(JSON.parse(wire), { maxBytes: 1e6 })],
]

/** An error's own `cause` field, read without inheritance. */
function causeOf(error: unknown): string {
  const cause = typeof error === 'object' && error !== null ? describe(error, 'cause') : undefined
  return cause !== undefined && hasOwn(cause, 'value') ? canonical(cause.value) : 'none'
}

function run(operation: () => unknown): string {
  try {
    return canonical(operation())
  } catch (error) {
    const text = error instanceof Error ? `${error.name}: ${error.message}` : String(error)
    return `throws ${text} ${causeOf(error)}`
  }
}

const expected = operations.map(([, operation]) => run(operation))
const failures: string[] = []
const prototypes: Array<[string, object]> = [
  ['Object', Object.prototype],
  ['Array', Array.prototype],
]
type Kind = 'accessor' | 'data' | 'false' | 'function' | 'read-only' | 'throwing'
const cases: Array<[PropertyKey, Kind]> = [
  ...PROBED.flatMap((name): Array<[PropertyKey, Kind]> => [
    [name, 'data'],
    [name, 'accessor'],
  ]),
  ...INDICES.map((index): [PropertyKey, Kind] => [index, 'data']),
  ...READ_ONLY.map((name): [PropertyKey, Kind] => [name, 'read-only']),
  ...FUNCTIONS.map((name): [PropertyKey, Kind] => [name, 'function']),
  // A getter that only Object.prototype holds is not the iterator's, so closing never runs it.
  ['return', 'throwing'],
  ...SYMBOLS.map((symbol): [PropertyKey, Kind] => [symbol, 'false']),
]
const inherited = (): string => 'inherited'
const throwing = (): never => {
  throw new Error('inherited getter')
}
const descriptors: Record<Kind, PropertyDescriptor> = {
  'accessor': { configurable: true, get: inherited, set: ignore },
  'data': { configurable: true, value: 'inherited', writable: true },
  'false': { configurable: true, value: false, writable: true },
  'function': { configurable: true, value: inherited, writable: true },
  'read-only': { configurable: true, value: 'inherited', writable: false },
  'throwing': { configurable: true, get: throwing, set: ignore },
}
for (let p = 0; p < prototypes.length; p++) {
  const [prototypeName, prototype] = prototypes[p]
  for (let c = 0; c < cases.length; c++) {
    const [name, kind] = cases[c]
    if (hasOwn(prototype, name)) continue
    Reflect.defineProperty(prototype, name, bare({ ...descriptors[kind] }))
    for (let index = 0; index < operations.length; index++) {
      const actual = run(operations[index][1])
      if (actual !== expected[index])
        failures.push(
          `${prototypeName}.prototype.${String(name)} ${kind}: ${operations[index][0]} ${actual.slice(0, 120)}`,
        )
    }
    Reflect.deleteProperty(prototype, name)
  }
}

// Data keys on Object.prototype, as a setter or read-only, as any code or a hardened environment
// can leave them: every object the library creates still holds its own data and no setter runs.
// Recipes that assign a key their object lacks follow assignment semantics, so they are left out,
// as are the keys `reconcile` adds to a kept object, which a prototype accessor rejects.
const COPYING = new Set(['produce/iterate', 'produce/search'])
const DATA_KEYS = Array.from({ length: 54 }, (_, index) => index).filter(
  (index) => ![16, 17, 19, 22, 25].includes(index),
)
let setterCalls = 0
const countSetter = (): void => {
  setterCalls += 1
}
for (let k = 0; k < DATA_KEYS.length; k++) {
  const name = K(DATA_KEYS[k])
  for (let readonly = 0; readonly < 2; readonly++) {
    Reflect.defineProperty(
      Object.prototype,
      name,
      bare(
        readonly === 1
          ? { configurable: true, value: 'inherited', writable: false }
          : { configurable: true, set: countSetter, get: () => 'inherited' },
      ),
    )
    for (let index = 0; index < operations.length; index++) {
      if (COPYING.has(operations[index][0])) continue
      const actual = run(operations[index][1])
      if (actual !== expected[index])
        failures.push(
          `Object.prototype.${name} ${readonly === 1 ? 'read-only' : 'setter'}: ${operations[index][0]} ${actual.slice(0, 120)}`,
        )
    }
    Reflect.deleteProperty(Object.prototype, name)
  }
}
if (setterCalls !== 0) failures.push(`Object.prototype setters ran ${setterCalls} times`)

export const result = { cases: cases.length + 2 * DATA_KEYS.length, failures }
