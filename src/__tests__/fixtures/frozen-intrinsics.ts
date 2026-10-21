// Child-process driver for standard-prototypes.spec.ts, run under `node --frozen-intrinsics`,
// where every method of a standard prototype is an accessor whose setter defines the key on its
// receiver. The spec imports it in a child process and reads `result` from standard output.
import { deserialize, produce, reconcile, serialize, snapshot } from '../../index'

const KEYS = [
  'toString',
  'valueOf',
  'constructor',
  'hasOwnProperty',
  'isPrototypeOf',
  'toLocaleString',
  '__defineGetter__',
]

const holds = (object: Record<string, unknown>, key: string, value: unknown): boolean =>
  Object.hasOwn(object, key) && object[key] === value

/** Whether assignment leaves an own data property holding the value, or throws. */
function assigned(assign: () => Record<string, unknown>, key: string): string {
  try {
    return holds(assign(), key, 42) ? 'own' : 'lost'
  } catch (error) {
    return `throws ${error instanceof Error ? error.name : String(error)}`
  }
}

/** Every new object the library builds from a source holding the key. */
function copies(key: string): Array<Record<string, unknown>> {
  const source = (): Record<string, unknown> => ({ [key]: 42, nested: { [key]: 42 } })
  const kept: Record<string, unknown> = { other: 1 }
  reconcile(kept, { added: source(), other: 1 })
  return [
    snapshot(source()) as Record<string, unknown>,
    deserialize(JSON.parse(JSON.stringify(serialize(source()))), { maxBytes: 1e5 }) as Record<
      string,
      unknown
    >,
    kept.added as Record<string, unknown>,
    produce(source(), (draft) => {
      draft.other = 1
      return draft
    }),
  ]
}

const failures: string[] = []
const base: Record<string, unknown> = { other: 1 }
for (const key of KEYS) {
  const plain = assigned(() => {
    const object: Record<string, unknown> = { other: 1 }
    object[key] = 42
    return object
  }, key)
  const draft = assigned(
    () =>
      produce(base, (value) => {
        value[key] = 42
        return value
      }),
    key,
  )
  if (draft !== plain) failures.push(`${key}: assignment ${plain}, in a recipe ${draft}`)
  try {
    for (const copy of copies(key))
      if (!holds(copy, key, 42) || !holds(copy.nested as Record<string, unknown>, key, 42))
        failures.push(`${key}: a copy lost it`)
  } catch (error) {
    failures.push(`${key}: copying throws ${String(error)}`)
  }
}

export const result = { cases: KEYS.length, failures }
