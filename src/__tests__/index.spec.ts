import { deepSignal } from 'alien-deepsignals'
import { assert, describe, it } from 'vitest'
import { isReactive, reactive } from 'vue'
import { reconcile, snapshot as takeSnapshot } from '../index'

const returnOne = () => 1

interface ObjectSurface {
  list: unknown[]
  nested: object
}

interface ObjectSurfaceCase {
  name: string
  createLive: <T extends object>(value: T) => T
  verifyLiveValue?: (value: ObjectSurface) => void
  verifySnapshotValue?: (value: ObjectSurface) => void
}

interface SelfReferentialRoot {
  nested: {
    count: number
  }
  self?: SelfReferentialRoot
}

interface ReconcileCollectionTopologyGraph {
  collection: unknown
  shared: {
    count: number
  }
}

interface ReconcileCollectionTopologyCase {
  name: string
  create: () => {
    current: ReconcileCollectionTopologyGraph
    next: ReconcileCollectionTopologyGraph
    readCollectionEntry: (result: ReconcileCollectionTopologyGraph) => unknown
  }
}

interface ReconcileEqualFastPathTopologyCase {
  name: string
  createSharedNextCase: () => {
    current: { left: unknown; right: unknown }
    next: { left: unknown; right: unknown }
    assertResult: (result: { left: unknown; right: unknown }) => void
  }
  createSplitNextCase: () => {
    current: { left: unknown; right: unknown }
    next: { left: unknown; right: unknown }
    assertResult: (result: { left: unknown; right: unknown }) => void
  }
}

interface SnapshotAliasingCase {
  name: string
  create: () => {
    live: Record<string, unknown>
    assertAliasing: (snapshot: Record<string, unknown>) => void
  }
}

interface ReconcileObjectKindReplacementCase {
  name: string
  create: () => {
    current: object
    next: object
    assertResult: (result: unknown) => void
  }
}

interface ReconcileTopologySplitCase {
  name: string
  create: () => {
    current: { keep: true; left: unknown; right: unknown }
    next: { keep: true; left: unknown; right: unknown }
    assertResult: (result: { keep: true; left: unknown; right: unknown }) => void
  }
}

type SupportedSpecValue = unknown

const createRandom = (seed: number): (() => number) => {
  let state = seed >>> 0

  return () => {
    state += 1_831_565_813
    let value = state
    value = Math.imul(value ^ (value >>> 15), value | 1)
    value ^= value + Math.imul(value ^ (value >>> 7), value | 61)
    return ((value ^ (value >>> 14)) >>> 0) / 4_294_967_296
  }
}

const shuffle = <T>(values: readonly T[], random: () => number): T[] => {
  const result = [...values]

  for (let index = result.length - 1; index > 0; index -= 1) {
    const target = Math.floor(random() * (index + 1))
    const current = result[index]
    result[index] = result[target]
    result[target] = current
  }

  return result
}

const buildObjectFromStringEntries = (
  entries: ReadonlyArray<readonly [string, unknown]>,
): Record<string, unknown> => {
  const result: Record<string, unknown> = {}

  for (const [key, value] of entries) {
    result[key] = value
  }

  return result
}

const buildObjectFromEntries = (
  entries: ReadonlyArray<readonly [PropertyKey, unknown]>,
): { [key: string]: unknown; [key: symbol]: unknown } => {
  const result: { [key: string]: unknown; [key: symbol]: unknown } = {}

  for (const [key, value] of entries) {
    result[key] = value
  }

  return result
}

const createSparseArray = <T>(
  entries: ReadonlyArray<readonly [number, T]>,
  length: number,
): Array<T | undefined> => {
  const result = new Array<T | undefined>(length)

  for (const [index, value] of entries) {
    result[index] = value
  }

  return result
}

const presentIndices = (value: readonly unknown[]): number[] => {
  const result: number[] = []

  for (let index = 0; index < value.length; index += 1) {
    if (index in value) {
      result.push(index)
    }
  }

  return result
}

const keyLabels = (value: object): string[] =>
  Reflect.ownKeys(value).map((key) =>
    typeof key === 'symbol' ? `symbol:${key.description ?? ''}` : key,
  )

const bytesOfArrayBuffer = (value: ArrayBuffer): number[] => Array.from(new Uint8Array(value))

const bytesOfDataView = (value: DataView): number[] =>
  Array.from(new Uint8Array(value.buffer, value.byteOffset, value.byteLength))

const isSupportedSpecObject = (
  value: SupportedSpecValue,
): value is Exclude<SupportedSpecValue, null> => typeof value === 'object' && value !== null

const isSupportedSpecTypedArray = (value: SupportedSpecValue): value is Uint16Array | Uint8Array =>
  value instanceof Uint8Array || value instanceof Uint16Array

const assertEquivalentSupportedGraph = (
  actual: SupportedSpecValue,
  expected: SupportedSpecValue,
  seenActualToExpected = new WeakMap<object, object>(),
  seenExpectedToActual = new WeakMap<object, object>(),
): void => {
  if (!isSupportedSpecObject(actual) || !isSupportedSpecObject(expected)) {
    assert.equal(Object.is(actual, expected), true)
    return
  }

  const actualObject = actual as object
  const expectedObject = expected as object
  const pairedExpected = seenActualToExpected.get(actualObject)
  const pairedActual = seenExpectedToActual.get(expectedObject)

  if (pairedExpected !== undefined || pairedActual !== undefined) {
    assert.equal(pairedExpected, expectedObject)
    assert.equal(pairedActual, actualObject)
    return
  }

  seenActualToExpected.set(actualObject, expectedObject)
  seenExpectedToActual.set(expectedObject, actualObject)

  assert.equal(Array.isArray(actual), Array.isArray(expected))

  if (Array.isArray(actual) && Array.isArray(expected)) {
    assert.equal(actual.length, expected.length)
    assert.deepEqual(presentIndices(actual), presentIndices(expected))

    for (let index = 0; index < expected.length; index += 1) {
      if (index in expected) {
        assertEquivalentSupportedGraph(
          actual[index],
          expected[index],
          seenActualToExpected,
          seenExpectedToActual,
        )
      }
    }

    return
  }

  assert.equal(actual instanceof Date, expected instanceof Date)

  if (actual instanceof Date && expected instanceof Date) {
    assert.equal(actual.getTime(), expected.getTime())
    return
  }

  assert.equal(isSupportedSpecTypedArray(actual), isSupportedSpecTypedArray(expected))

  if (isSupportedSpecTypedArray(actual) && isSupportedSpecTypedArray(expected)) {
    assert.equal(actual.constructor, expected.constructor)
    assert.deepEqual(Array.from(actual), Array.from(expected))
    return
  }

  const actualKeys = Reflect.ownKeys(actualObject)
  const expectedKeys = Reflect.ownKeys(expectedObject)

  assert.equal(actualKeys.length, expectedKeys.length)

  for (let index = 0; index < expectedKeys.length; index += 1) {
    assert.equal(actualKeys[index], expectedKeys[index])
    assertEquivalentSupportedGraph(
      (actual as Record<PropertyKey, SupportedSpecValue>)[expectedKeys[index]],
      (expected as Record<PropertyKey, SupportedSpecValue>)[expectedKeys[index]],
      seenActualToExpected,
      seenExpectedToActual,
    )
  }
}

const createRandomPrimitiveValue = (random: () => number): SupportedSpecValue => {
  const choice = Math.floor(random() * 5)

  switch (choice) {
    case 0:
      return Math.floor(random() * 1000)
    case 1:
      return `value-${Math.floor(random() * 1000)}`
    case 2:
      return random() < 0.5
    case 3:
      return null
    default:
      return `tag-${Math.floor(random() * 32)}`
  }
}

const createRandomTypedArrayValue = (random: () => number): Uint16Array | Uint8Array => {
  const length = Math.floor(random() * 4) + 1
  const values = Array.from({ length }, () => Math.floor(random() * 32))

  return random() < 0.5 ? new Uint8Array(values) : new Uint16Array(values)
}

type RandomSupportedValueFactory = (random: () => number, depth: number) => SupportedSpecValue

const createRandomSupportedValue: RandomSupportedValueFactory = (random, depth) => {
  if (depth <= 0) {
    const terminalChoice = Math.floor(random() * 4)

    switch (terminalChoice) {
      case 0:
        return createRandomPrimitiveValue(random)
      case 1:
        return new Date(Date.UTC(2024, Math.floor(random() * 12), Math.floor(random() * 28) + 1))
      case 2:
        return createRandomTypedArrayValue(random)
      default:
        return createRandomPrimitiveValue(random)
    }
  }

  const choice = Math.floor(random() * 5)

  switch (choice) {
    case 0:
      return createRandomPrimitiveValue(random)
    case 1:
      return createRandomArrayValue(random, depth)
    case 2:
      return createRandomPlainObjectValue(random, depth)
    case 3:
      return new Date(Date.UTC(2024, Math.floor(random() * 12), Math.floor(random() * 28) + 1))
    default:
      return createRandomTypedArrayValue(random)
  }
}

function createRandomArrayValue(random: () => number, depth: number): SupportedSpecValue[] {
  const length = Math.floor(random() * 5)
  const result = new Array<SupportedSpecValue>(length)

  for (let index = 0; index < length; index += 1) {
    if (random() < 0.7) {
      result[index] = createRandomSupportedValue(random, depth - 1)
    }
  }

  return result
}

function createRandomPlainObjectValue(
  random: () => number,
  depth: number,
): Record<PropertyKey, SupportedSpecValue> {
  const keyPool = ['alpha', 'bravo', 'charlie', 'delta', 'echo'] as const
  const keys = shuffle(keyPool, random).slice(0, Math.floor(random() * (keyPool.length + 1)))
  const sharedPool: SupportedSpecValue[] =
    depth === 0
      ? []
      : Array.from({ length: 3 }, () => createRandomSupportedValue(random, depth - 1))
  const result: Record<PropertyKey, SupportedSpecValue> = {}

  for (let index = 0; index < keys.length; index += 1) {
    const key = keys[index]
    result[key] =
      sharedPool.length > 0 && random() < 0.5
        ? sharedPool[Math.floor(random() * sharedPool.length)]!
        : createRandomSupportedValue(random, depth - 1)
  }

  return result
}

const createPlainObjectExpectationCase = (
  random: () => number,
): {
  current: Record<PropertyKey, SupportedSpecValue>
  next: Record<PropertyKey, SupportedSpecValue>
} => ({
  current: createRandomPlainObjectValue(random, 2),
  next: createRandomPlainObjectValue(random, 2),
})

const createPlainLive = <T extends object>(value: T): T => value

const createVueLive = <T extends object>(value: T): T => {
  const live: unknown = reactive(value)
  return live as T
}

const createDeepSignalLive = <T extends object>(value: T): T => {
  const live: unknown = deepSignal(value)
  return live as T
}

const objectSurfaceCases: ObjectSurfaceCase[] = [
  {
    createLive: createPlainLive,
    name: 'plain objects',
  },
  {
    createLive: createVueLive,
    name: 'vue reactive objects',
    verifyLiveValue: (value) => {
      assert.equal(isReactive(value), true)
      assert.equal(isReactive(value.nested), true)
      assert.equal(isReactive(value.list), true)
    },
    verifySnapshotValue: (value) => {
      assert.equal(isReactive(value), false)
      assert.equal(isReactive(value.nested), false)
      assert.equal(isReactive(value.list), false)
    },
  },
  {
    createLive: createDeepSignalLive,
    name: 'alien-deepsignals objects',
  },
]

const reconcileCollectionTopologyCases: ReconcileCollectionTopologyCase[] = [
  {
    name: 'Map values',
    create: () => {
      const currentShared = { count: 0 }
      const nextShared = { count: 1 }

      return {
        current: {
          collection: new Map<string, { count: number }>([['shared', currentShared]]),
          shared: currentShared,
        },
        next: {
          collection: new Map<string, { count: number }>([['shared', nextShared]]),
          shared: nextShared,
        },
        readCollectionEntry: (result) =>
          (result.collection as Map<string, { count: number }>).get('shared'),
      }
    },
  },
  {
    name: 'Map keys',
    create: () => {
      const currentShared = { count: 0 }
      const nextShared = { count: 1 }

      return {
        current: {
          collection: new Map<{ count: number }, string>([[currentShared, 'shared']]),
          shared: currentShared,
        },
        next: {
          collection: new Map<{ count: number }, string>([[nextShared, 'shared']]),
          shared: nextShared,
        },
        readCollectionEntry: (result) =>
          [...(result.collection as Map<{ count: number }, string>).keys()][0],
      }
    },
  },
  {
    name: 'Set entries',
    create: () => {
      const currentShared = { count: 0 }
      const nextShared = { count: 1 }

      return {
        current: {
          collection: new Set([currentShared]),
          shared: currentShared,
        },
        next: {
          collection: new Set([nextShared]),
          shared: nextShared,
        },
        readCollectionEntry: (result) => [...(result.collection as Set<unknown>).values()][0],
      }
    },
  },
]

const snapshotAliasingCases: SnapshotAliasingCase[] = [
  {
    name: 'an ArrayBuffer and a typed-array view',
    create: () => {
      const buffer = new ArrayBuffer(8)
      const bytes = new Uint8Array(buffer)
      bytes.set([10, 20, 30, 40, 50, 60, 70, 80])
      const view = new Uint8Array(buffer, 2, 3)

      return {
        live: { buffer, view },
        assertAliasing: (snapshot) => {
          const snapshotBuffer = snapshot.buffer as ArrayBuffer
          const snapshotView = snapshot.view as Uint8Array

          assert.equal(snapshotView.buffer, snapshotBuffer)
          assert.deepEqual(Array.from(snapshotView), [30, 40, 50])
        },
      }
    },
  },
  {
    name: 'multiple typed-array views that share one buffer',
    create: () => {
      const buffer = new ArrayBuffer(8)
      const bytes = new Uint8Array(buffer)
      bytes.set([1, 2, 3, 4, 5, 6, 7, 8])
      const left = new Uint8Array(buffer, 0, 4)
      const right = new Uint8Array(buffer, 4, 4)

      return {
        live: { left, right },
        assertAliasing: (snapshot) => {
          const snapshotLeft = snapshot.left as Uint8Array
          const snapshotRight = snapshot.right as Uint8Array

          assert.equal(snapshotLeft.buffer, snapshotRight.buffer)
          assert.deepEqual(Array.from(snapshotLeft), [1, 2, 3, 4])
          assert.deepEqual(Array.from(snapshotRight), [5, 6, 7, 8])
        },
      }
    },
  },
  {
    name: 'typed-array and DataView aliases into one buffer',
    create: () => {
      const buffer = new ArrayBuffer(8)
      const bytes = new Uint8Array(buffer)
      bytes.set([11, 12, 13, 14, 15, 16, 17, 18])
      const typed = new Uint8Array(buffer, 1, 4)
      const view = new DataView(buffer, 2, 3)

      return {
        live: { typed, view },
        assertAliasing: (snapshot) => {
          const snapshotTyped = snapshot.typed as Uint8Array
          const snapshotView = snapshot.view as DataView

          assert.equal(snapshotTyped.buffer, snapshotView.buffer)
          assert.deepEqual(Array.from(snapshotTyped), [12, 13, 14, 15])
          assert.deepEqual(
            Array.from(
              new Uint8Array(snapshotView.buffer, snapshotView.byteOffset, snapshotView.byteLength),
            ),
            [13, 14, 15],
          )
        },
      }
    },
  },
]

const reconcileObjectKindReplacementCases: ReconcileObjectKindReplacementCase[] = [
  {
    name: 'plain object to array',
    create: () => {
      const current = { a: 1 }
      const next = [10, 20]

      return {
        current,
        next,
        assertResult: (result) => {
          assert.equal(Array.isArray(result), true)
          assert.deepEqual(result, next)
          assert.notEqual(result, current)
        },
      }
    },
  },
  {
    name: 'array to plain object',
    create: () => {
      const current = [1, 2]
      const next = { a: 1 }

      return {
        current,
        next,
        assertResult: (result) => {
          assert.equal(Array.isArray(result), false)
          assert.equal(Object.getPrototypeOf(result as object), Object.prototype)
          assert.deepEqual(result, next)
          assert.notEqual(result, current)
        },
      }
    },
  },
  {
    name: 'Date to plain object',
    create: () => {
      const current = new Date('2020-01-01T00:00:00.000Z')
      const next = { a: 1 }

      return {
        current,
        next,
        assertResult: (result) => {
          assert.equal(result instanceof Date, false)
          assert.equal(Object.getPrototypeOf(result as object), Object.prototype)
          assert.deepEqual(result, next)
          assert.notEqual(result, current)
        },
      }
    },
  },
  {
    name: 'plain object to Date',
    create: () => {
      const current = { a: 1 }
      const next = new Date('2020-01-01T00:00:00.000Z')

      return {
        current,
        next,
        assertResult: (result) => {
          assert.equal(result instanceof Date, true)
          assert.equal((result as Date).getTime(), next.getTime())
          assert.notEqual(result, current)
        },
      }
    },
  },
]

const reconcileEqualFastPathTopologyCases: ReconcileEqualFastPathTopologyCase[] = [
  {
    name: 'plain-object properties',
    createSharedNextCase: () => {
      const shared = { value: 1 }

      return {
        current: { left: shared, right: { value: 0 } },
        next: { left: shared, right: shared },
        assertResult: (result) => {
          assert.equal(result.left, result.right)
          assert.deepEqual(result.left, { value: 1 })
        },
      }
    },
    createSplitNextCase: () => {
      const shared = { value: 0 }

      return {
        current: { left: shared, right: shared },
        next: { left: shared, right: { value: 2 } },
        assertResult: (result) => {
          assert.notEqual(result.left, result.right)
          assert.deepEqual(result.left, { value: 0 })
          assert.deepEqual(result.right, { value: 2 })
        },
      }
    },
  },
  {
    name: 'array entries',
    createSharedNextCase: () => {
      const shared = { value: 1 }

      return {
        current: { left: [shared, { value: 0 }], right: { value: -1 } },
        next: { left: [shared, shared], right: shared },
        assertResult: (result) => {
          const left = result.left as unknown[]
          assert.equal(left[0], left[1])
          assert.equal(left[0], result.right)
          assert.deepEqual(left[0], { value: 1 })
        },
      }
    },
    createSplitNextCase: () => {
      const shared = { value: 0 }

      return {
        current: { left: [shared, shared], right: shared },
        next: { left: [shared, { value: 2 }], right: { value: 3 } },
        assertResult: (result) => {
          const left = result.left as unknown[]
          assert.equal(left[0], shared)
          assert.notEqual(left[0], left[1])
          assert.notEqual(left[0], result.right)
          assert.deepEqual(left[0], { value: 0 })
          assert.deepEqual(left[1], { value: 2 })
          assert.deepEqual(result.right, { value: 3 })
        },
      }
    },
  },
  {
    name: 'Map values',
    createSharedNextCase: () => {
      const shared = { value: 1 }

      return {
        current: {
          left: new Map<string, unknown>([
            ['shared', shared],
            // eslint-disable-next-line perfectionist/sort-maps
            ['other', { value: 0 }],
          ]),
          right: { value: -1 },
        },
        next: {
          left: new Map<string, unknown>([
            ['shared', shared],
            // eslint-disable-next-line perfectionist/sort-maps
            ['other', shared],
          ]),
          right: shared,
        },
        assertResult: (result) => {
          const left = result.left as Map<string, unknown>
          assert.equal(left.get('shared'), left.get('other'))
          assert.equal(left.get('shared'), result.right)
          assert.deepEqual(left.get('shared'), { value: 1 })
        },
      }
    },
    createSplitNextCase: () => {
      const shared = { value: 0 }

      return {
        current: {
          left: new Map<string, unknown>([
            ['shared', shared],
            // eslint-disable-next-line perfectionist/sort-maps
            ['other', shared],
          ]),
          right: shared,
        },
        next: {
          left: new Map<string, unknown>([
            ['shared', shared],
            // eslint-disable-next-line perfectionist/sort-maps
            ['other', { value: 2 }],
          ]),
          right: { value: 3 },
        },
        assertResult: (result) => {
          const left = result.left as Map<string, unknown>
          assert.equal(left.get('shared'), shared)
          assert.notEqual(left.get('shared'), left.get('other'))
          assert.notEqual(left.get('shared'), result.right)
          assert.deepEqual(left.get('shared'), { value: 0 })
          assert.deepEqual(left.get('other'), { value: 2 })
          assert.deepEqual(result.right, { value: 3 })
        },
      }
    },
  },
  {
    name: 'Map keys',
    createSharedNextCase: () => {
      const shared = { value: 1 }

      return {
        current: {
          left: new Map<object, string>([
            [shared, 'shared'],
            // eslint-disable-next-line perfectionist/sort-maps
            [{ value: 0 }, 'other'],
          ]),
          right: { value: -1 },
        },
        next: {
          left: new Map<object, string>([
            [shared, 'shared'],
            [shared, 'other'],
          ]),
          right: shared,
        },
        assertResult: (result) => {
          const leftEntries = [...(result.left as Map<object, string>).keys()]
          assert.equal(leftEntries.length, 1)
          assert.equal(leftEntries[0], result.right)
          assert.deepEqual(leftEntries[0], { value: 1 })
        },
      }
    },
    createSplitNextCase: () => {
      const shared = { value: 0 }

      return {
        current: {
          left: new Map<object, string>([[shared, 'shared']]),
          right: shared,
        },
        next: {
          left: new Map<object, string>([
            [shared, 'shared'],
            // eslint-disable-next-line perfectionist/sort-maps
            [{ value: 2 }, 'other'],
          ]),
          right: { value: 3 },
        },
        assertResult: (result) => {
          const leftKeys = [...(result.left as Map<object, string>).keys()]
          assert.equal(leftKeys[0], shared)
          assert.notEqual(leftKeys[0], leftKeys[1])
          assert.notEqual(leftKeys[0], result.right)
          assert.deepEqual(leftKeys[0], { value: 0 })
          assert.deepEqual(leftKeys[1], { value: 2 })
          assert.deepEqual(result.right, { value: 3 })
        },
      }
    },
  },
  {
    name: 'Set entries',
    createSharedNextCase: () => {
      const shared = { value: 1 }

      return {
        current: {
          // eslint-disable-next-line perfectionist/sort-sets
          left: new Set<unknown>([shared, { value: 0 }]),
          right: { value: -1 },
        },
        next: { left: new Set<unknown>([shared]), right: shared },
        assertResult: (result) => {
          const leftEntry = [...(result.left as Set<unknown>).values()][0]
          assert.equal(leftEntry, result.right)
          assert.deepEqual(leftEntry, { value: 1 })
        },
      }
    },
    createSplitNextCase: () => {
      const shared = { value: 0 }

      return {
        current: { left: new Set<unknown>([shared]), right: shared },
        next: { left: new Set<unknown>([shared]), right: { value: 2 } },
        assertResult: (result) => {
          const leftEntry = [...(result.left as Set<unknown>).values()][0]
          assert.equal(leftEntry, shared)
          assert.notEqual(leftEntry, result.right)
          assert.deepEqual(leftEntry, { value: 0 })
          assert.deepEqual(result.right, { value: 2 })
        },
      }
    },
  },
]

const reconcileTopologySplitCases: ReconcileTopologySplitCase[] = [
  {
    name: 'plain objects',
    create: () => {
      const shared = { value: 0 }
      const current = { keep: true as const, left: shared, right: shared }
      const next = { keep: true as const, left: { value: 1 }, right: { value: 2 } }

      return {
        current,
        next,
        assertResult: (result) => {
          assert.notEqual(result.left, result.right)
          assert.deepEqual(result.left, { value: 1 })
          assert.deepEqual(result.right, { value: 2 })
        },
      }
    },
  },
  {
    name: 'arrays',
    create: () => {
      const shared = [0]
      const current = { keep: true as const, left: shared, right: shared }
      const next = { keep: true as const, left: [1], right: [2] }

      return {
        current,
        next,
        assertResult: (result) => {
          assert.notEqual(result.left, result.right)
          assert.deepEqual(result.left, [1])
          assert.deepEqual(result.right, [2])
        },
      }
    },
  },
  {
    name: 'Date instances',
    create: () => {
      const shared = new Date('2020-01-01T00:00:00.000Z')
      const current = { keep: true as const, left: shared, right: shared }
      const next = {
        keep: true as const,
        left: new Date('2020-01-02T00:00:00.000Z'),
        right: new Date('2020-01-03T00:00:00.000Z'),
      }

      return {
        current,
        next,
        assertResult: (result) => {
          assert.notEqual(result.left, result.right)
          assert.equal((result.left as Date).getTime(), next.left.getTime())
          assert.equal((result.right as Date).getTime(), next.right.getTime())
        },
      }
    },
  },
  {
    name: 'Map instances',
    create: () => {
      const shared = new Map<string, number>([['value', 0]])
      const current = { keep: true as const, left: shared, right: shared }
      const next = {
        keep: true as const,
        left: new Map<string, number>([['value', 1]]),
        right: new Map<string, number>([['value', 2]]),
      }

      return {
        current,
        next,
        assertResult: (result) => {
          assert.notEqual(result.left, result.right)
          assert.deepEqual([...(result.left as Map<string, number>).entries()], [['value', 1]])
          assert.deepEqual([...(result.right as Map<string, number>).entries()], [['value', 2]])
        },
      }
    },
  },
  {
    name: 'Set instances',
    create: () => {
      const shared = new Set<number>([0])
      const current = { keep: true as const, left: shared, right: shared }
      const next = {
        keep: true as const,
        left: new Set<number>([1]),
        right: new Set<number>([2]),
      }

      return {
        current,
        next,
        assertResult: (result) => {
          assert.notEqual(result.left, result.right)
          assert.deepEqual([...(result.left as Set<number>).values()], [1])
          assert.deepEqual([...(result.right as Set<number>).values()], [2])
        },
      }
    },
  },
  {
    name: 'ArrayBuffer instances',
    create: () => {
      const shared = new Uint8Array([0, 1]).buffer
      const current = { keep: true as const, left: shared, right: shared }
      const next = {
        keep: true as const,
        left: new Uint8Array([1, 2]).buffer,
        right: new Uint8Array([3, 4]).buffer,
      }

      return {
        current,
        next,
        assertResult: (result) => {
          assert.notEqual(result.left, result.right)
          assert.deepEqual(bytesOfArrayBuffer(result.left as ArrayBuffer), [1, 2])
          assert.deepEqual(bytesOfArrayBuffer(result.right as ArrayBuffer), [3, 4])
        },
      }
    },
  },
  {
    name: 'DataView instances',
    create: () => {
      const shared = new DataView(new Uint8Array([0, 1]).buffer)
      const current = { keep: true as const, left: shared, right: shared }
      const next = {
        keep: true as const,
        left: new DataView(new Uint8Array([1, 2]).buffer),
        right: new DataView(new Uint8Array([3, 4]).buffer),
      }

      return {
        current,
        next,
        assertResult: (result) => {
          assert.notEqual(result.left, result.right)
          assert.deepEqual(bytesOfDataView(result.left as DataView), [1, 2])
          assert.deepEqual(bytesOfDataView(result.right as DataView), [3, 4])
        },
      }
    },
  },
  {
    name: 'typed-array instances',
    create: () => {
      const shared = new Uint8Array([0, 1])
      const current = { keep: true as const, left: shared, right: shared }
      const next = {
        keep: true as const,
        left: new Uint8Array([1, 2]),
        right: new Uint8Array([3, 4]),
      }

      return {
        current,
        next,
        assertResult: (result) => {
          assert.notEqual(result.left, result.right)
          assert.deepEqual(Array.from(result.left as Uint8Array), [1, 2])
          assert.deepEqual(Array.from(result.right as Uint8Array), [3, 4])
        },
      }
    },
  },
]

const runObjectSurfaceContract = (testCase: ObjectSurfaceCase) => {
  it('snapshot preserves input key order across permutations and detaches nested state', () => {
    const entries = [
      ['delta', 4],
      ['alpha', 1],
      ['charlie', 3],
      ['bravo', 2],
    ] as const
    const random = createRandom(424_242)

    for (let index = 0; index < 16; index += 1) {
      const candidateEntries = shuffle(entries, random)
      const live = testCase.createLive({
        list: [1, 2],
        nested: buildObjectFromStringEntries(candidateEntries),
      })
      const snapshot = takeSnapshot(live) as {
        list: number[]
        nested: Record<string, unknown>
      }

      assert.notEqual(snapshot, live)
      assert.notEqual(snapshot.nested, live.nested)
      assert.notEqual(snapshot.list, live.list)
      testCase.verifySnapshotValue?.(snapshot)
      assert.deepEqual(
        Object.keys(snapshot.nested),
        candidateEntries.map(([key]) => key),
      )
    }
  })

  it('snapshot preserves sparse array holes and exact length', () => {
    const live = testCase.createLive({
      list: createSparseArray(
        [
          [1, 20],
          [3, 40],
        ],
        5,
      ),
      nested: { keep: true },
    })
    const snapshot = takeSnapshot(live) as {
      list: Array<number | undefined>
      nested: {
        keep: boolean
      }
    }

    assert.equal(snapshot.list.length, 5)
    assert.deepEqual(presentIndices(snapshot.list), [1, 3])
    assert.equal(0 in snapshot.list, false)
    assert.equal(2 in snapshot.list, false)
    assert.equal(4 in snapshot.list, false)
    assert.deepEqual(snapshot.nested, { keep: true })
  })

  it('reconcile preserves compatible root and subtree identities', () => {
    const live = testCase.createLive<{
      keep: number
      list: number[]
      nested: {
        count: number
        flag: boolean
      }
      add?: number
      remove?: number
    }>({
      keep: 1,
      list: [1, 2],
      nested: { count: 0, flag: true },
      remove: 2,
    })
    const listReference = live.list
    const nestedReference = live.nested

    testCase.verifyLiveValue?.(live)

    const result = reconcile(live, {
      add: 3,
      keep: 9,
      list: [1, 2, 3],
      nested: { count: 1, flag: false },
    }) as typeof live

    assert.equal(result, live)
    assert.equal(result.list, listReference)
    assert.equal(result.nested, nestedReference)
    testCase.verifyLiveValue?.(result)
    assert.deepEqual(result, {
      add: 3,
      keep: 9,
      list: [1, 2, 3],
      nested: { count: 1, flag: false },
    })
    assert.equal('remove' in result, false)
  })

  it('reconcile preserves next key order instead of retaining previous object order', () => {
    const entries = [
      ['delta', 4],
      ['alpha', 1],
      ['charlie', 3],
      ['bravo', 2],
    ] as const
    const random = createRandom(20_260_217)

    for (let index = 0; index < 16; index += 1) {
      const candidateEntries = shuffle(entries, random)
      const current = testCase.createLive(buildObjectFromStringEntries(entries))
      const next = buildObjectFromStringEntries(candidateEntries)
      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.deepEqual(
        Object.keys(result),
        candidateEntries.map(([key]) => key),
      )
    }
  })

  it('reconcile preserves sparse array holes instead of materializing undefined entries', () => {
    const current = testCase.createLive({
      list: [10, 20, 30],
      nested: { keep: true },
    })
    const listReference = current.list
    const nextList = createSparseArray(
      [
        [1, 20],
        [4, 50],
      ],
      5,
    )

    const result = reconcile(current, {
      list: nextList,
      nested: { keep: true },
    }) as typeof current

    assert.equal(result, current)
    assert.equal(result.list, listReference)
    assert.equal(result.list.length, 5)
    assert.deepEqual(presentIndices(result.list), [1, 4])
    assert.equal(0 in result.list, false)
    assert.equal(2 in result.list, false)
    assert.equal(3 in result.list, false)
    assert.equal(result.list[1], 20)
    assert.equal(result.list[4], 50)
  })

  it('reconcile preserves shared references from the next graph', () => {
    const current = testCase.createLive({
      left: { note: 'left', value: 0 },
      nested: { count: 0 },
      right: { note: 'right', value: 0 },
    })
    const shared = { note: 'shared', value: 2 }

    const result = reconcile(current, {
      left: shared,
      nested: { count: 1 },
      right: shared,
    })

    assert.equal(result, current)
    assert.equal(result.left, result.right)
    assert.deepEqual(result.left, { note: 'shared', value: 2 })
    assert.deepEqual(result.nested, { count: 1 })
  })
}

describe('context runtime direct contracts', () => {
  describe('primitive values', () => {
    it('snapshot returns primitive values unchanged', () => {
      assert.equal(takeSnapshot(1), 1)
      assert.equal(takeSnapshot('x'), 'x')
      assert.equal(takeSnapshot(true), true)
      assert.equal(takeSnapshot(null), null)
    })

    it('reconcile returns parentContext immediately when both inputs are the same value', () => {
      const current = { keep: true }

      assert.equal(reconcile(current, current), current)
      assert.equal(Object.is(reconcile(Number.NaN, Number.NaN), Number.NaN), true)
    })

    it('reconcile returns nextContext across primitive boundaries', () => {
      assert.equal(reconcile(1, 2), 2)
      assert.equal(reconcile('left', 'right'), 'right')
      assert.equal(reconcile(null, false), false)
      assert.equal(reconcile({ keep: true }, 2), 2)

      const nextObject = { keep: true }
      assert.equal(reconcile(1, nextObject), nextObject)
      assert.equal(reconcile(null, nextObject), nextObject)
    })
  })

  describe.each(objectSurfaceCases)('$name', (testCase) => {
    runObjectSurfaceContract(testCase)
  })

  describe('plain-object exotic shapes', () => {
    it('snapshot preserves cycles, shared references, prototype, and symbol-key order', () => {
      const first = Symbol('first')
      const second = Symbol('second')
      const prototype = { marker: true }
      const shared = { count: 1 }
      const live = Object.create(prototype) as {
        alpha: number
        [first]: string
        left: {
          count: number
        }
        omega: number
        right: {
          count: number
        }
        [second]: string
        self: unknown
      }

      live.omega = 1
      live.alpha = 2
      live[first] = 'first'
      live[second] = 'second'
      live.left = shared
      live.right = shared
      live.self = live

      const snapshot = takeSnapshot(live) as typeof live

      assert.notEqual(snapshot, live)
      assert.equal(Object.getPrototypeOf(snapshot), prototype)
      assert.equal(snapshot.left, snapshot.right)
      assert.equal(snapshot.self, snapshot)
      assert.deepEqual(keyLabels(snapshot), keyLabels(live))
    })

    it('snapshot clones dates, maps, sets, buffers, typed arrays, and data views', () => {
      const typed = new Uint8Array([1, 2, 3])
      const viewBuffer = new Uint8Array([4, 5, 6]).buffer
      const mapEntries = [
        ['beta', { value: 2 }],
        ['alpha', { value: 1 }],
      ] as const
      const setValues = ['beta', 'alpha'] as const
      const live = {
        buffer: typed.buffer.slice(0),
        date: new Date('2024-01-02T03:04:05.000Z'),
        map: new Map<unknown, unknown>(mapEntries),
        set: new Set(setValues),
        typed: new Uint16Array([7, 8, 9]),
        view: new DataView(viewBuffer),
      }

      const snapshot = takeSnapshot(live) as typeof live

      assert.notEqual(snapshot.date, live.date)
      assert.equal(snapshot.date.getTime(), live.date.getTime())
      assert.notEqual(snapshot.map, live.map)
      assert.deepEqual([...snapshot.map.keys()], ['beta', 'alpha'])
      assert.notEqual(snapshot.set, live.set)
      assert.deepEqual([...snapshot.set.values()], ['beta', 'alpha'])
      assert.notEqual(snapshot.buffer, live.buffer)
      assert.deepEqual(
        Array.from(new Uint8Array(snapshot.buffer)),
        Array.from(new Uint8Array(live.buffer)),
      )
      assert.notEqual(snapshot.typed, live.typed)
      assert.equal(snapshot.typed.constructor, Uint16Array)
      assert.deepEqual(Array.from(snapshot.typed), [7, 8, 9])
      assert.notEqual(snapshot.view, live.view)
      assert.deepEqual(
        Array.from(
          new Uint8Array(snapshot.view.buffer, snapshot.view.byteOffset, snapshot.view.byteLength),
        ),
        [4, 5, 6],
      )
    })

    for (const testCase of snapshotAliasingCases) {
      it(`snapshot preserves aliasing for ${testCase.name}`, () => {
        const { assertAliasing, live } = testCase.create()
        const snapshot = takeSnapshot(live) as Record<string, unknown>

        assertAliasing(snapshot)
      })
    }

    it('snapshot preserves function values by reference', () => {
      const snapshot = takeSnapshot({ bad: returnOne }) as { bad: () => number }

      assert.equal(typeof snapshot.bad, 'function')
      assert.equal(snapshot.bad, returnOne)
      assert.equal(snapshot.bad(), 1)
    })

    it('reconcile can publish function values and snapshot preserves them by reference', () => {
      const current: {
        keep?: boolean
        bad?: () => number
      } = { keep: true }
      const published = reconcile(current, { bad: returnOne }) as typeof current

      assert.equal(published, current)
      assert.equal(published.bad, returnOne)

      const snapshot = takeSnapshot(published) as typeof published
      assert.equal(snapshot.bad, returnOne)
    })

    it('reconcile preserves self cycles while keeping the root identity', () => {
      const current: SelfReferentialRoot = {
        nested: { count: 0 },
      }
      current.self = current

      const next: SelfReferentialRoot = {
        nested: { count: 1 },
      }
      next.self = next

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal(result.self, result)
      assert.deepEqual(result.nested, { count: 1 })
    })

    it('reconcile updates supported exotic subtrees in place when possible', () => {
      const typedReference = new Uint8Array([1, 2])
      const bufferReference = new Uint8Array([3, 4]).buffer
      const viewReference = new DataView(new Uint8Array([5, 6]).buffer)
      const current = {
        buffer: bufferReference,
        date: new Date('2024-01-01T00:00:00.000Z'),
        map: new Map<string, unknown>([['alpha', { value: 0 }]]),
        set: new Set<number>([1, 2]),
        typed: typedReference,
        view: viewReference,
      }
      const dateReference = current.date
      const mapReference = current.map
      const setReference = current.set

      const next = {
        buffer: new Uint8Array([7, 8]).buffer,
        date: new Date('2024-01-03T00:00:00.000Z'),
        map: new Map<string, unknown>([
          ['alpha', { value: 1 }],
          ['beta', { value: 2 }],
        ]),
        set: new Set<number>([1, 3]),
        typed: new Uint8Array([9, 10]),
        view: new DataView(new Uint8Array([11, 12]).buffer),
      }

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal(result.date, dateReference)
      assert.equal(result.map, mapReference)
      assert.equal(result.set, setReference)
      assert.equal(result.buffer, bufferReference)
      assert.equal(result.typed, typedReference)
      assert.equal(result.view, viewReference)
      assert.equal(result.date.getTime(), next.date.getTime())
      assert.deepEqual([...result.map.keys()], ['alpha', 'beta'])
      assert.deepEqual([...result.set.values()], [1, 3])
      assert.deepEqual(Array.from(new Uint8Array(result.buffer)), [7, 8])
      assert.deepEqual(Array.from(result.typed), [9, 10])
      assert.deepEqual(
        Array.from(
          new Uint8Array(result.view.buffer, result.view.byteOffset, result.view.byteLength),
        ),
        [11, 12],
      )
    })

    it('reconcile avoids array index writes when entries reconcile in place', () => {
      const shared = { count: 0 }
      const list = new Proxy([shared, 2], {
        set(target, property, value, receiver) {
          if (property === '0' || property === '1') {
            writes += 1
          }

          return Reflect.set(target, property, value, receiver)
        },
      }) as Array<number | { count: number }>
      let writes = 0
      const current = { list }
      const listReference = current.list

      const result = reconcile(current, {
        list: [{ count: 1 }, 2],
      })

      assert.equal(result, current)
      assert.equal(result.list, listReference)
      assert.equal(result.list[0], shared)
      assert.deepEqual(result.list, [{ count: 1 }, 2])
      assert.equal(writes, 0)
    })

    it('reconcile avoids rebuilding a Map when entries reconcile to existing identities', () => {
      const shared = { count: 0 }
      const map = new Map<string, { count: number }>([['shared', shared]])
      const clear = map.clear.bind(map)
      const set = map.set.bind(map)
      let clears = 0
      let sets = 0

      map.clear = () => {
        clears += 1
        return clear()
      }
      map.set = (key: string, value: { count: number }) => {
        sets += 1
        return set(key, value)
      }

      const current = { map }
      const mapReference = current.map

      const result = reconcile(current, {
        map: new Map<string, { count: number }>([['shared', { count: 1 }]]),
      })

      assert.equal(result, current)
      assert.equal(result.map, mapReference)
      assert.equal(result.map.get('shared'), shared)
      assert.deepEqual(result.map.get('shared'), { count: 1 })
      assert.equal(clears, 0)
      assert.equal(sets, 0)
    })

    it('reconcile rebuilds a growing Map while preserving an unchanged reconciled prefix', () => {
      const shared = { count: 0 }
      const map = new Map<string, number | { count: number }>([['shared', shared]])
      const clear = map.clear.bind(map)
      const set = map.set.bind(map)
      let clears = 0
      let sets = 0

      map.clear = () => {
        clears += 1
        return clear()
      }
      map.set = (key: string, value: number | { count: number }) => {
        sets += 1
        return set(key, value)
      }

      const current = { map }
      const mapReference = current.map

      /* eslint-disable perfectionist/sort-maps */
      const result = reconcile(current, {
        map: new Map<string, number | { count: number }>([
          ['shared', { count: 1 }],
          ['added', 2],
        ]),
      })
      /* eslint-enable perfectionist/sort-maps */

      assert.equal(result, current)
      assert.equal(result.map, mapReference)
      assert.equal(result.map.get('shared'), shared)
      assert.deepEqual(
        [...result.map.entries()],
        [
          ['shared', shared],
          ['added', 2],
        ],
      )
      assert.deepEqual(shared, { count: 1 })
      assert.equal(clears, 1)
      assert.equal(sets, 2)
    })

    it('reconcile shrinks a Map while preserving an unchanged reconciled prefix', () => {
      const shared = { count: 0 }
      const removed = { count: 9 }
      /* eslint-disable perfectionist/sort-maps */
      const map = new Map<string, { count: number }>([
        ['shared', shared],
        ['removed', removed],
      ])
      /* eslint-enable perfectionist/sort-maps */
      const clear = map.clear.bind(map)
      const set = map.set.bind(map)
      let clears = 0
      let sets = 0

      map.clear = () => {
        clears += 1
        return clear()
      }
      map.set = (key: string, value: { count: number }) => {
        sets += 1
        return set(key, value)
      }

      const current = { map }
      const mapReference = current.map

      const result = reconcile(current, {
        map: new Map<string, { count: number }>([['shared', { count: 1 }]]),
      })

      assert.equal(result, current)
      assert.equal(result.map, mapReference)
      assert.equal(result.map.get('shared'), shared)
      assert.deepEqual([...result.map.entries()], [['shared', shared]])
      assert.deepEqual(shared, { count: 1 })
      assert.equal(result.map.has('removed'), false)
      assert.equal(clears, 1)
      assert.equal(sets, 1)
    })

    it('reconcile grows a Set in place when next has additional entries', () => {
      const current = {
        set: new Set<number | undefined>([1]),
      }
      const setReference = current.set

      const result = reconcile(current, {
        set: new Set<number | undefined>([1, undefined]),
      })

      assert.equal(result, current)
      assert.equal(result.set, setReference)
      assert.deepEqual([...result.set.values()], [1, undefined])
    })

    it('reconcile avoids rebuilding a Set when entries reconcile to existing identities', () => {
      const shared = { count: 0 }
      const set = new Set<{ count: number }>([shared])
      const clear = set.clear.bind(set)
      const add = set.add.bind(set)
      let clears = 0
      let adds = 0

      set.clear = () => {
        clears += 1
        return clear()
      }
      set.add = (value: { count: number }) => {
        adds += 1
        return add(value)
      }

      const current = { set }
      const setReference = current.set

      const result = reconcile(current, {
        set: new Set<{ count: number }>([{ count: 1 }]),
      })
      const [entry] = result.set.values()

      assert.equal(result, current)
      assert.equal(result.set, setReference)
      assert.equal(entry, shared)
      assert.deepEqual(entry, { count: 1 })
      assert.equal(clears, 0)
      assert.equal(adds, 0)
    })

    it('reconcile rebuilds a growing Set while preserving an unchanged reconciled prefix', () => {
      const shared = { count: 0 }
      const set = new Set<number | { count: number }>([shared])
      const clear = set.clear.bind(set)
      const add = set.add.bind(set)
      let clears = 0
      let adds = 0

      set.clear = () => {
        clears += 1
        return clear()
      }
      set.add = (value: number | { count: number }) => {
        adds += 1
        return add(value)
      }

      const current = { set }
      const setReference = current.set

      const result = reconcile(current, {
        set: new Set<number | { count: number }>([{ count: 1 }, 2]),
      })

      assert.equal(result, current)
      assert.equal(result.set, setReference)
      assert.deepEqual([...result.set.values()], [shared, 2])
      assert.deepEqual(shared, { count: 1 })
      assert.equal(clears, 1)
      assert.equal(adds, 2)
    })

    it('reconcile shrinks a Set while preserving an unchanged reconciled prefix', () => {
      const shared = { count: 0 }
      const removed = { count: 9 }
      // eslint-disable-next-line perfectionist/sort-sets
      const set = new Set<{ count: number }>([shared, removed])
      const clear = set.clear.bind(set)
      const add = set.add.bind(set)
      let clears = 0
      let adds = 0

      set.clear = () => {
        clears += 1
        return clear()
      }
      set.add = (value: { count: number }) => {
        adds += 1
        return add(value)
      }

      const current = { set }
      const setReference = current.set

      const result = reconcile(current, {
        set: new Set<{ count: number }>([{ count: 1 }]),
      })

      assert.equal(result, current)
      assert.equal(result.set, setReference)
      assert.deepEqual([...result.set.values()], [shared])
      assert.deepEqual(shared, { count: 1 })
      assert.equal(result.set.has(removed), false)
      assert.equal(clears, 1)
      assert.equal(adds, 1)
    })

    it('reconcile grows an array while preserving an unchanged reconciled prefix', () => {
      const shared = { count: 0 }
      let prefixWrites = 0
      const list = new Proxy([shared], {
        set(target, property, value, receiver) {
          if (property === '0') {
            prefixWrites += 1
          }

          return Reflect.set(target, property, value, receiver)
        },
      }) as Array<number | { count: number }>
      const current = { list }
      const listReference = current.list

      const result = reconcile(current, {
        list: [{ count: 1 }, 2],
      })

      assert.equal(result, current)
      assert.equal(result.list, listReference)
      assert.equal(result.list[0], shared)
      assert.deepEqual(result.list, [shared, 2])
      assert.deepEqual(shared, { count: 1 })
      assert.equal(prefixWrites, 0)
    })

    it('reconcile shrinks an array while preserving an unchanged reconciled prefix', () => {
      const shared = { count: 0 }
      let prefixWrites = 0
      const list = new Proxy([shared, 2], {
        set(target, property, value, receiver) {
          if (property === '0') {
            prefixWrites += 1
          }

          return Reflect.set(target, property, value, receiver)
        },
      }) as Array<number | { count: number }>
      const current = { list }
      const listReference = current.list

      const result = reconcile(current, {
        list: [{ count: 1 }],
      }) as typeof current

      assert.equal(result, current)
      assert.equal(result.list, listReference)
      assert.equal(result.list[0], shared)
      assert.deepEqual(result.list, [shared])
      assert.deepEqual(shared, { count: 1 })
      assert.equal(result.list.length, 1)
      assert.equal(1 in result.list, false)
      assert.equal(prefixWrites, 0)
    })

    it('reconcile rebuilds a Map when a key reconciles to a replacement identity', () => {
      const currentKey = new Uint8Array([1, 2])
      const current = {
        map: new Map<object, string>([[currentKey, 'value']]),
      }
      const mapReference = current.map

      const result = reconcile(current, {
        map: new Map<object, string>([[new Uint16Array([3, 4]), 'value']]),
      })
      const resultKey = Array.from(result.map.keys())[0] as Uint16Array | Uint8Array

      assert.equal(result, current)
      assert.equal(result.map, mapReference)
      assert.notEqual(resultKey, currentKey)
      assert.equal(resultKey.constructor, Uint16Array)
      assert.deepEqual(Array.from(resultKey), [3, 4])
    })

    it('reconcile rebuilds a Map when a value reconciles to a replacement identity', () => {
      const currentValue = new Uint8Array([1, 2])
      const current = {
        map: new Map<string, Uint16Array | Uint8Array>([['value', currentValue]]),
      }
      const mapReference = current.map

      const result = reconcile(current, {
        map: new Map<string, Uint16Array | Uint8Array>([['value', new Uint16Array([3, 4])]]),
      })
      const resultValue = result.map.get('value')!

      assert.equal(result, current)
      assert.equal(result.map, mapReference)
      assert.notEqual(resultValue, currentValue)
      assert.equal(resultValue.constructor, Uint16Array)
      assert.deepEqual(Array.from(resultValue), [3, 4])
    })

    it('reconcile keeps rebuilding a Map after an early changed entry forces lazy rebuild', () => {
      const currentValue = new Uint8Array([1, 2])
      const current = {
        map: new Map<string, number | Uint16Array | Uint8Array>([
          ['changed', currentValue],
          ['tail', 9],
        ]),
      }
      const mapReference = current.map

      const result = reconcile(current, {
        map: new Map<string, number | Uint16Array | Uint8Array>([
          ['changed', new Uint16Array([3, 4])],
          ['tail', 9],
        ]),
      })
      const resultEntries = [...result.map.entries()]
      const resultValue = result.map.get('changed')!

      assert.equal(result, current)
      assert.equal(result.map, mapReference)
      assert.notEqual(resultValue, currentValue)
      assert.equal((resultValue as Uint16Array).constructor, Uint16Array)
      assert.deepEqual(Array.from(resultValue as Uint16Array), [3, 4])
      assert.deepEqual(resultEntries, [
        ['changed', resultValue],
        ['tail', 9],
      ])
    })

    it('reconcile keeps rebuilding a Set after an early changed entry forces lazy rebuild', () => {
      const currentEntry = new Uint8Array([1, 2])
      const current = {
        // eslint-disable-next-line perfectionist/sort-sets
        set: new Set<number | Uint16Array | Uint8Array>([currentEntry, 9]),
      }
      const setReference = current.set

      const result = reconcile(current, {
        // eslint-disable-next-line perfectionist/sort-sets
        set: new Set<number | Uint16Array | Uint8Array>([new Uint16Array([3, 4]), 9]),
      })
      const resultEntries = [...result.set.values()]
      const resultEntry = resultEntries[0] as Uint16Array | Uint8Array

      assert.equal(result, current)
      assert.equal(result.set, setReference)
      assert.notEqual(resultEntry, currentEntry)
      assert.equal(resultEntry.constructor, Uint16Array)
      assert.deepEqual(Array.from(resultEntry), [3, 4])
      assert.deepEqual(resultEntries, [resultEntry, 9])
    })

    for (const testCase of reconcileCollectionTopologyCases) {
      it(`reconcile preserves shared topology through ${testCase.name}`, () => {
        const { current, next, readCollectionEntry } = testCase.create()
        const result = reconcile(current, next)

        assert.equal(result, current)
        assert.equal(result.shared.count, 1)
        assert.equal(readCollectionEntry(result), result.shared)
      })
    }

    for (const testCase of reconcileTopologySplitCases) {
      it(`reconcile splits previously shared ${testCase.name} when next requires distinct nodes`, () => {
        const { assertResult, current, next } = testCase.create()
        const result = reconcile(current, next)

        assert.equal(result, current)
        assertResult(result)
      })
    }

    for (const testCase of reconcileEqualFastPathTopologyCases) {
      it(`reconcile preserves next-sharing through equal fast paths for ${testCase.name}`, () => {
        const { assertResult, current, next } = testCase.createSharedNextCase()
        const result = reconcile(current, next)

        assert.equal(result, current)
        assertResult(result)
      })

      it(`reconcile preserves splitting through equal fast paths for ${testCase.name}`, () => {
        const { assertResult, current, next } = testCase.createSplitNextCase()
        const result = reconcile(current, next)

        assert.equal(result, current)
        assertResult(result)
      })
    }

    it('reconcile preserves sparse array holes when splitting a shared array subtree', () => {
      const shared = createSparseArray([[0, 0]], 3)
      const current = {
        left: shared,
        right: shared,
      }
      const next = {
        left: createSparseArray([[1, 10]], 3),
        right: createSparseArray([[2, 20]], 4),
      }

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.notEqual(result.left, result.right)
      assert.deepEqual(presentIndices(result.left), [1])
      assert.deepEqual(presentIndices(result.right), [2])
      assert.equal(result.left.length, 3)
      assert.equal(result.right.length, 4)
      assert.equal(result.left[1], 10)
      assert.equal(result.right[2], 20)
    })

    it('reconcile reuses an already-mapped result when an equal fast path reaches the same next object later', () => {
      const shared = { value: 1 }
      const current = {
        alpha: { value: 0 },
        beta: shared,
      }
      const next = {
        alpha: shared,
        beta: shared,
      }

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal(result.alpha, result.beta)
      assert.notEqual(result.alpha, shared)
      assert.deepEqual(result.alpha, { value: 1 })
    })

    it('reconcile splits an equal fast path when the current object was already consumed by a different next object', () => {
      const shared = { value: 0 }
      const current = {
        alpha: shared,
        beta: shared,
      }
      const next = {
        alpha: { value: 0 },
        beta: shared,
      }

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.notEqual(result.alpha, result.beta)
      assert.equal(result.alpha, shared)
      assert.notEqual(result.beta, shared)
      assert.deepEqual(result.alpha, { value: 0 })
      assert.deepEqual(result.beta, { value: 0 })
    })

    it('reconcile preserves next-sharing across a primitive-to-object replacement boundary', () => {
      const nextSharedChild = { count: 1 }
      const current = {
        left: 0,
        right: { child: { count: 0 } },
      }
      const next = {
        left: { child: nextSharedChild },
        right: { child: nextSharedChild },
      }

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal(result.left.child, result.right.child)
      assert.deepEqual(result.left, { child: { count: 1 } })
      assert.deepEqual(result.right, { child: { count: 1 } })
    })

    it('reconcile preserves reconciled back-references through an object-kind replacement boundary', () => {
      const current = {
        child: [],
      }
      const next = {
        child: {
          parent: undefined as unknown,
        },
      }
      next.child.parent = next

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal(result.child.parent, result)
    })

    it('reconcile preserves next-sharing inside split plain-object replacements', () => {
      const currentSharedChild = { count: 0 }
      const currentSharedParent = { child: currentSharedChild, label: 'current' }
      const current = {
        left: currentSharedParent,
        right: currentSharedParent,
      }
      const nextSharedChild = { count: 1 }
      const next = {
        left: { child: nextSharedChild, label: 'left' },
        right: { child: nextSharedChild, label: 'right' },
      }

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.notEqual(result.left, result.right)
      assert.equal(result.left.child, result.right.child)
      assert.deepEqual(result.left, { child: { count: 1 }, label: 'left' })
      assert.deepEqual(result.right, { child: { count: 1 }, label: 'right' })
    })

    it('reconcile replaces only an incompatible object-kind subtree while preserving the parent and siblings', () => {
      const currentKeep = { count: 0 }
      const currentChange = { value: 1 }
      const current = {
        change: currentChange,
        keep: currentKeep,
      }

      const result = reconcile(current, {
        change: [10, 20],
        keep: { count: 1 },
      })

      assert.equal(result, current)
      assert.equal(result.keep, currentKeep)
      assert.notEqual(result.change, currentChange)
      assert.deepEqual(result.change, [10, 20])
      assert.deepEqual(result.keep, { count: 1 })
    })

    it('reconcile preserves the next plain-object prototype across a replacement boundary', () => {
      const prototype = { marker: true }
      const nextChild = Object.create(prototype) as {
        value: number
      }
      nextChild.value = 1

      const current = {
        child: 0,
      }
      const result = reconcile(current, {
        child: nextChild,
      })

      assert.equal(result, current)
      assert.notEqual(result.child, nextChild)
      assert.equal(Object.getPrototypeOf(result.child), prototype)
      assert.equal(Object.hasOwn(result.child, 'value'), true)
      assert.deepEqual(Reflect.ownKeys(result.child), ['value'])
      assert.equal(result.child.value, 1)
    })

    it('reconcile publishes function values inside replacement subtrees and snapshot preserves them', () => {
      const current = {
        child: 0,
      }
      const result = reconcile(current, {
        child: { bad: returnOne },
      })

      assert.equal(result, current)
      assert.equal(result.child.bad, returnOne)

      const snapshot = takeSnapshot(result) as typeof result
      assert.equal(snapshot.child.bad, returnOne)
    })

    it('reconcile preserves ArrayBuffer and DataView aliasing when next aliases them', () => {
      const current = {
        buffer: new Uint8Array([1, 2, 3, 4]).buffer,
        view: new DataView(new Uint8Array([9, 9, 9, 9]).buffer),
      }
      const nextBuffer = new Uint8Array([5, 6, 7, 8]).buffer
      const next = {
        buffer: nextBuffer,
        view: new DataView(nextBuffer),
      }

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal(result.view.buffer, result.buffer)
      assert.deepEqual(bytesOfArrayBuffer(result.buffer), [5, 6, 7, 8])
      assert.deepEqual(bytesOfDataView(result.view), [5, 6, 7, 8])
    })

    it('reconcile preserves ArrayBuffer and DataView non-aliasing when next separates them', () => {
      const sharedBuffer = new Uint8Array([1, 2, 3, 4]).buffer
      const current = {
        buffer: sharedBuffer,
        view: new DataView(sharedBuffer),
      }
      const next = {
        buffer: new Uint8Array([5, 6, 7, 8]).buffer,
        view: new DataView(new Uint8Array([9, 10, 11, 12]).buffer),
      }

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.notEqual(result.view.buffer, result.buffer)
      assert.deepEqual(bytesOfArrayBuffer(result.buffer), [5, 6, 7, 8])
      assert.deepEqual(bytesOfDataView(result.view), [9, 10, 11, 12])
    })

    it('reconcile preserves ArrayBuffer and typed-array aliasing when next aliases them', () => {
      const current = {
        buffer: new Uint8Array([1, 2, 3, 4]).buffer,
        typed: new Uint8Array(new Uint8Array([9, 9, 9, 9]).buffer),
      }
      const nextBuffer = new Uint8Array([5, 6, 7, 8]).buffer
      const next = {
        buffer: nextBuffer,
        typed: new Uint8Array(nextBuffer),
      }

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal(result.typed.buffer, result.buffer)
      assert.deepEqual(bytesOfArrayBuffer(result.buffer), [5, 6, 7, 8])
      assert.deepEqual(Array.from(result.typed), [5, 6, 7, 8])
    })

    it('reconcile preserves ArrayBuffer and typed-array non-aliasing when next separates them', () => {
      const sharedBuffer = new Uint8Array([1, 2, 3, 4]).buffer
      const current = {
        buffer: sharedBuffer,
        typed: new Uint8Array(sharedBuffer),
      }
      const next = {
        buffer: new Uint8Array([5, 6, 7, 8]).buffer,
        typed: new Uint8Array(new Uint8Array([9, 10, 11, 12]).buffer),
      }

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.notEqual(result.typed.buffer, result.buffer)
      assert.deepEqual(bytesOfArrayBuffer(result.buffer), [5, 6, 7, 8])
      assert.deepEqual(Array.from(result.typed), [9, 10, 11, 12])
    })

    it('reconcile preserves DataView and typed-array aliasing when next aliases them', () => {
      const current = {
        typed: new Uint8Array(new Uint8Array([1, 2, 3, 4]).buffer),
        view: new DataView(new Uint8Array([9, 9, 9, 9]).buffer),
      }
      const nextBuffer = new Uint8Array([5, 6, 7, 8]).buffer
      const next = {
        typed: new Uint8Array(nextBuffer),
        view: new DataView(nextBuffer),
      }

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal(result.typed.buffer, result.view.buffer)
      assert.deepEqual(Array.from(result.typed), [5, 6, 7, 8])
      assert.deepEqual(bytesOfDataView(result.view), [5, 6, 7, 8])
    })

    it('reconcile preserves binary view topology through the equal-buffer fast path', () => {
      const sharedBuffer = new Uint8Array([5, 6, 7, 8]).buffer
      const current = {
        typed: new Uint8Array(sharedBuffer),
        view: new DataView(sharedBuffer),
      }
      const typedReference = current.typed
      const viewReference = current.view
      const next = {
        typed: new Uint8Array(sharedBuffer),
        view: new DataView(sharedBuffer),
      }

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal(result.typed, typedReference)
      assert.equal(result.view, viewReference)
      assert.equal(result.typed.buffer, result.view.buffer)
      assert.equal(result.typed.buffer, sharedBuffer)
      assert.deepEqual(Array.from(result.typed), [5, 6, 7, 8])
      assert.deepEqual(bytesOfDataView(result.view), [5, 6, 7, 8])
    })

    it('reconcile preserves DataView and typed-array non-aliasing when next separates them', () => {
      const sharedBuffer = new Uint8Array([1, 2, 3, 4]).buffer
      const current = {
        typed: new Uint8Array(sharedBuffer),
        view: new DataView(sharedBuffer),
      }
      const next = {
        typed: new Uint8Array(new Uint8Array([5, 6, 7, 8]).buffer),
        view: new DataView(new Uint8Array([9, 10, 11, 12]).buffer),
      }

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.notEqual(result.typed.buffer, result.view.buffer)
      assert.deepEqual(Array.from(result.typed), [5, 6, 7, 8])
      assert.deepEqual(bytesOfDataView(result.view), [9, 10, 11, 12])
    })

    it('reconcile preserves aliasing across multiple typed arrays that share one next buffer', () => {
      const current = {
        left: new Uint8Array(new Uint8Array([1, 2, 3, 4]).buffer, 0, 2),
        right: new Uint8Array(new Uint8Array([9, 9, 9, 9]).buffer, 2, 2),
      }
      const nextBuffer = new Uint8Array([5, 6, 7, 8]).buffer
      const next = {
        left: new Uint8Array(nextBuffer, 0, 2),
        right: new Uint8Array(nextBuffer, 2, 2),
      }

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal(result.left.buffer, result.right.buffer)
      assert.deepEqual(Array.from(result.left), [5, 6])
      assert.deepEqual(Array.from(result.right), [7, 8])
    })

    it('reconcile preserves non-aliasing across typed arrays when next separates their buffers', () => {
      const sharedBuffer = new Uint8Array([1, 2, 3, 4]).buffer
      const current = {
        left: new Uint8Array(sharedBuffer, 0, 2),
        right: new Uint8Array(sharedBuffer, 2, 2),
      }
      const next = {
        left: new Uint8Array(new Uint8Array([5, 6]).buffer),
        right: new Uint8Array(new Uint8Array([7, 8]).buffer),
      }

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.notEqual(result.left.buffer, result.right.buffer)
      assert.deepEqual(Array.from(result.left), [5, 6])
      assert.deepEqual(Array.from(result.right), [7, 8])
    })

    it('reconcile preserves aliasing across multiple DataViews that share one next buffer', () => {
      const current = {
        left: new DataView(new Uint8Array([1, 2, 3, 4]).buffer, 0, 2),
        right: new DataView(new Uint8Array([9, 9, 9, 9]).buffer, 2, 2),
      }
      const nextBuffer = new Uint8Array([5, 6, 7, 8]).buffer
      const next = {
        left: new DataView(nextBuffer, 0, 2),
        right: new DataView(nextBuffer, 2, 2),
      }

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal(result.left.buffer, result.right.buffer)
      assert.deepEqual(bytesOfDataView(result.left), [5, 6])
      assert.deepEqual(bytesOfDataView(result.right), [7, 8])
    })

    it('reconcile preserves non-aliasing across DataViews when next separates their buffers', () => {
      const sharedBuffer = new Uint8Array([1, 2, 3, 4]).buffer
      const current = {
        left: new DataView(sharedBuffer, 0, 2),
        right: new DataView(sharedBuffer, 2, 2),
      }
      const next = {
        left: new DataView(new Uint8Array([5, 6]).buffer),
        right: new DataView(new Uint8Array([7, 8]).buffer),
      }

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.notEqual(result.left.buffer, result.right.buffer)
      assert.deepEqual(bytesOfDataView(result.left), [5, 6])
      assert.deepEqual(bytesOfDataView(result.right), [7, 8])
    })

    it('reconcile preserves the full backing buffer for a DataView replacement with a larger aliased buffer', () => {
      const current = {
        view: new DataView(new Uint8Array([1, 2]).buffer, 0, 2),
      }
      const nextBuffer = new Uint8Array([4, 5, 6, 7]).buffer
      const next = {
        view: new DataView(nextBuffer, 1, 2),
      }

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal(result.view.byteOffset, 1)
      assert.equal(result.view.byteLength, 2)
      assert.equal(result.view.buffer.byteLength, 4)
      assert.deepEqual(bytesOfArrayBuffer(result.view.buffer), [4, 5, 6, 7])
      assert.deepEqual(bytesOfDataView(result.view), [5, 6])
    })

    it('reconcile reuses one DataView replacement when the same next DataView is referenced twice', () => {
      const current = {
        left: new DataView(new Uint8Array([1, 2, 3, 4]).buffer, 0, 2),
        right: new DataView(new Uint8Array([9, 9, 9, 9]).buffer, 0, 2),
      }
      const sharedNextView = new DataView(new Uint8Array([5, 6, 7, 8]).buffer, 1, 2)
      const next = {
        left: sharedNextView,
        right: sharedNextView,
      }

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal(result.left, result.right)
      assert.notEqual(result.left, sharedNextView)
      assert.equal(result.left.byteOffset, 1)
      assert.equal(result.left.byteLength, 2)
      assert.deepEqual(bytesOfArrayBuffer(result.left.buffer), [5, 6, 7, 8])
      assert.deepEqual(bytesOfDataView(result.left), [6, 7])
    })

    it('reconcile reuses one typed-array replacement when the same next typed array is referenced twice', () => {
      const current = {
        left: new Uint8Array(new Uint8Array([1, 2, 3, 4]).buffer, 0, 2),
        right: new Uint8Array(new Uint8Array([9, 9, 9, 9]).buffer, 0, 2),
      }
      const sharedNextTyped = new Uint8Array(new Uint8Array([5, 6, 7, 8]).buffer, 1, 2)
      const next = {
        left: sharedNextTyped,
        right: sharedNextTyped,
      }

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal(result.left, result.right)
      assert.notEqual(result.left, sharedNextTyped)
      assert.equal(result.left.byteOffset, 1)
      assert.equal(result.left.byteLength, 2)
      assert.deepEqual(bytesOfArrayBuffer(result.left.buffer), [5, 6, 7, 8])
      assert.deepEqual(Array.from(result.left), [6, 7])
    })

    it('reconcile replaces a typed-array view when next changes the byte offset', () => {
      const sharedBuffer = new Uint8Array([1, 2, 3, 4]).buffer
      const current = {
        typed: new Uint8Array(sharedBuffer, 0, 2),
      }
      const nextBuffer = new Uint8Array([5, 6, 7, 8]).buffer
      const next = {
        typed: new Uint8Array(nextBuffer, 1, 2),
      }
      const typedReference = current.typed

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.notEqual(result.typed, typedReference)
      assert.equal(result.typed.byteOffset, 1)
      assert.equal(result.typed.byteLength, 2)
      assert.deepEqual(bytesOfArrayBuffer(result.typed.buffer), [5, 6, 7, 8])
      assert.deepEqual(Array.from(result.typed), [6, 7])
    })

    for (const testCase of reconcileObjectKindReplacementCases) {
      it(`reconcile replaces the root on ${testCase.name} changes`, () => {
        const { assertResult, current, next } = testCase.create()
        const result = reconcile(current, next)

        assertResult(result)
      })
    }

    it('reconcile replaces only incompatible binary subtrees while preserving the parent object', () => {
      const current = {
        buffer: new Uint8Array([1, 2]).buffer,
        typed: new Uint8Array([3, 4]),
      }
      const parentReference = current
      const bufferReference = current.buffer
      const typedReference = current.typed

      const result = reconcile(current, {
        buffer: new Uint8Array([5, 6, 7, 8]).buffer,
        typed: new Uint16Array([9, 10]),
      }) as {
        buffer: ArrayBuffer
        typed: Uint16Array | Uint8Array
      }

      assert.equal(result, parentReference)
      assert.notEqual(result.buffer, bufferReference)
      assert.notEqual(result.typed, typedReference)
      assert.equal(result.typed.constructor, Uint16Array)
      assert.equal(result.buffer.byteLength, 4)
      assert.deepEqual(Array.from(new Uint8Array(result.buffer)), [5, 6, 7, 8])
      assert.deepEqual(Array.from(result.typed), [9, 10])
    })

    it('reconcile replaces incompatible binary views when byte lengths change', () => {
      const current = {
        typed: new Uint8Array([1, 2]),
        view: new DataView(new Uint8Array([3, 4]).buffer),
      }
      const parentReference = current
      const typedReference = current.typed
      const viewReference = current.view

      const result = reconcile(current, {
        typed: new Uint8Array([5, 6, 7]),
        view: new DataView(new Uint8Array([8, 9, 10]).buffer),
      }) as {
        typed: Uint8Array
        view: DataView
      }

      assert.equal(result, parentReference)
      assert.notEqual(result.typed, typedReference)
      assert.notEqual(result.view, viewReference)
      assert.equal(result.typed.constructor, Uint8Array)
      assert.equal(result.view.byteLength, 3)
      assert.deepEqual(Array.from(result.typed), [5, 6, 7])
      assert.deepEqual(
        Array.from(
          new Uint8Array(result.view.buffer, result.view.byteOffset, result.view.byteLength),
        ),
        [8, 9, 10],
      )
    })

    it('reconcile preserves key order for string and symbol keys', () => {
      const first = Symbol('first')
      const second = Symbol('second')
      const current = buildObjectFromEntries([
        ['alpha', 1],
        ['omega', 2],
        [first, 'first'],
        [second, 'second'],
      ])
      const next = buildObjectFromEntries([
        ['omega', 2],
        ['alpha', 1],
        [second, 'second'],
        [first, 'first'],
      ])

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.deepEqual(keyLabels(result), keyLabels(next))
    })

    it('reconcile preserves earlier replaced entries when a later key-order mismatch rebuilds', () => {
      const current = {
        alpha: new Uint8Array([1, 2]),
        bravo: 2,
        charlie: 3,
      }
      const alphaReference = current.alpha
      const next = buildObjectFromStringEntries([
        ['alpha', new Uint16Array([4, 5])],
        ['charlie', 3],
        ['bravo', 2],
      ]) as {
        alpha: Uint16Array
        bravo: number
        charlie: number
      }

      const result = reconcile(current, next) as {
        alpha: Uint16Array | Uint8Array
        bravo: number
        charlie: number
      }

      assert.equal(result, current)
      assert.notEqual(result.alpha, alphaReference)
      assert.equal(result.alpha.constructor, Uint16Array)
      assert.deepEqual(Array.from(result.alpha), [4, 5])
      assert.deepEqual(Object.keys(result), ['alpha', 'charlie', 'bravo'])
    })

    it('reconcile matches supported plain-object expectations across randomized graphs', () => {
      const random = createRandom(20_260_326)

      for (let index = 0; index < 200; index += 1) {
        const { current, next } = createPlainObjectExpectationCase(random)
        const actualCurrent = structuredClone(current)
        const actualNext = structuredClone(next)
        const actualResult = reconcile(actualCurrent, actualNext)

        assert.equal(actualResult, actualCurrent)
        assertEquivalentSupportedGraph(actualResult, actualNext)
      }
    })

    it('reconcile preserves non-enumerable descriptors for retained keys', () => {
      const current = {}
      Object.defineProperty(current, 'hidden', {
        configurable: true,
        enumerable: false,
        value: 1,
        writable: true,
      })

      const result = reconcile(current, { hidden: 2 }) as typeof current
      const descriptor = Object.getOwnPropertyDescriptor(result, 'hidden')

      assert.equal(result, current)
      assert.deepEqual(descriptor, {
        configurable: true,
        enumerable: false,
        value: 2,
        writable: true,
      })
    })

    it.fails('reconcile removes non-configurable keys absent from the next object', () => {
      const current = {}
      Object.defineProperty(current, 'fixed', {
        configurable: false,
        enumerable: true,
        value: 1,
        writable: true,
      })

      const result = reconcile(current, {})

      assert.equal(result, current)
      assert.equal('fixed' in result, false)
    })
  })
})
