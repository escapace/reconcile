import { assert, describe, it } from 'vitest'
import * as fc from 'fast-check'

import { createPatch, patch } from '../patch'
import { reconcile } from '../reconcile'
import { snapshot } from '../snapshot'

type Jsonish =
  | boolean
  | number
  | string
  | { readonly [key: string]: Jsonish }
  | { readonly type: string; readonly value?: unknown }
  | readonly Jsonish[]
  | null

const sharedFunction = () => 'stable'

const bytesOf = (buffer: ArrayBuffer): number[] => Array.from(new Uint8Array(buffer))

const bytesOfView = (view: ArrayBufferView): number[] =>
  Array.from(new Uint8Array(view.buffer, view.byteOffset, view.byteLength))

const cloneBufferFrom = (bytes: Uint8Array): ArrayBuffer => {
  const replacement = new Uint8Array(bytes.length)
  replacement.set(bytes)
  return replacement.buffer
}

const normalize = (value: unknown, seen = new Map<object, number>()): Jsonish => {
  if (value === null || typeof value === 'boolean' || typeof value === 'string') {
    return value
  }

  if (typeof value === 'number') {
    return Object.is(value, -0) ? { type: 'number', value: '-0' } : value
  }

  if (value === undefined) {
    return { type: 'undefined' }
  }

  if (typeof value === 'function') {
    return { type: 'function' }
  }

  if (typeof value === 'bigint') {
    return { type: 'bigint', value: value.toString() }
  }

  if (typeof value === 'symbol') {
    return { type: 'symbol', value: value.description }
  }

  if (typeof value !== 'object') {
    return { type: typeof value }
  }

  const knownReference = seen.get(value)

  if (knownReference !== undefined) {
    return { type: 'ref', value: knownReference }
  }

  seen.set(value, seen.size)

  if (value instanceof Date) {
    return { type: 'Date', value: value.getTime() }
  }

  if (value instanceof ArrayBuffer) {
    return { type: 'ArrayBuffer', value: bytesOf(value) }
  }

  if (value instanceof DataView) {
    return {
      type: 'DataView',
      value: {
        byteLength: value.byteLength,
        byteOffset: value.byteOffset,
        bytes: bytesOfView(value),
      },
    }
  }

  if (ArrayBuffer.isView(value)) {
    return {
      type: value.constructor.name,
      value: {
        byteLength: value.byteLength,
        byteOffset: value.byteOffset,
        bytes: bytesOfView(value),
      },
    }
  }

  if (Array.isArray(value)) {
    const items: Jsonish[] = []

    for (let index = 0; index < value.length; index += 1) {
      items.push(index in value ? normalize(value[index], seen) : { type: 'hole' })
    }

    return { type: 'Array', value: items }
  }

  if (value instanceof Map) {
    return {
      type: 'Map',
      value: Array.from(value, ([key, entry]) => [normalize(key, seen), normalize(entry, seen)]),
    }
  }

  if (value instanceof Set) {
    return { type: 'Set', value: Array.from(value, (entry) => normalize(entry, seen)) }
  }

  const record = value as Record<string, unknown>
  const normalized: Record<string, Jsonish> = {}

  for (const key of Object.keys(record)) {
    normalized[key] = normalize(record[key], seen)
  }

  return { type: 'Object', value: normalized }
}

const primitiveArbitrary = fc.oneof(
  fc.constant(null),
  fc.constant(undefined),
  fc.boolean(),
  fc.integer({ max: 1000, min: -1000 }),
  fc.string({ maxLength: 12 }),
  fc.constant(sharedFunction),
)

const binaryArbitrary = fc.uint8Array({ maxLength: 8, minLength: 1 })

const arrayBufferArbitrary = binaryArbitrary.map(cloneBufferFrom)
const dateArbitrary = fc.integer({ max: 4_102_444_800_000, min: 0 }).map((time) => new Date(time))
const dataViewArbitrary = binaryArbitrary.map((bytes) => new DataView(cloneBufferFrom(bytes)))
const typedArrayArbitrary = binaryArbitrary.map((bytes) => new Uint8Array(cloneBufferFrom(bytes)))

const supportedValueArbitrary = fc.letrec((tie) => ({
  array: fc.array(tie('value'), { maxLength: 3 }),
  map: fc
    .uniqueArray(fc.tuple(fc.string({ maxLength: 8 }), tie('value')), {
      maxLength: 3,
      selector: ([key]) => key,
    })
    .map((entries) => new Map<string, unknown>(entries)),
  object: fc.dictionary(fc.string({ maxLength: 8 }), tie('value'), { maxKeys: 3 }),
  set: fc.array(primitiveArbitrary, { maxLength: 3 }).map((values) => new Set(values)),
  special: fc.oneof(arrayBufferArbitrary, dataViewArbitrary, typedArrayArbitrary, dateArbitrary),
  value: fc.oneof(
    { depthSize: 'small', withCrossShrink: true },
    primitiveArbitrary,
    tie('special'),
    tie('array'),
    tie('object'),
    tie('map'),
    tie('set'),
  ),
})).value

type ContainerKind = 'array' | 'map' | 'object'
type SpecialKind = 'arrayBuffer' | 'dataView' | 'date' | 'typedArray'

const containerKindArbitrary = fc.constantFrom<ContainerKind>('array', 'map', 'object')
const specialKindArbitrary = fc.constantFrom<SpecialKind>(
  'arrayBuffer',
  'dataView',
  'date',
  'typedArray',
)
const deepPathArbitrary = fc
  .integer({ max: 8, min: 1 })
  .chain((depth) => fc.array(containerKindArbitrary, { maxLength: depth, minLength: depth }))

const wrapDeepChild = (kind: ContainerKind, child: unknown): unknown => {
  switch (kind) {
    case 'array':
      return [child, child, new Set([child])]
    case 'map':
      return new Map<string, unknown>([
        ['alias', child],
        ['child', child],
        ['set', new Set([child])],
      ])
    case 'object':
      return { alias: child, child, set: new Set([child]) }
  }
}

const buildDeepValue = (path: readonly ContainerKind[], leaf: unknown): unknown =>
  path.reduceRight((child, kind) => wrapDeepChild(kind, child), leaf)

const childAt = (container: unknown, kind: ContainerKind): unknown => {
  switch (kind) {
    case 'array':
      return (container as unknown[])[0]
    case 'map':
      return (container as Map<string, unknown>).get('child')
    case 'object':
      return (container as { child: unknown }).child
  }
}

const navigateDeep = (root: unknown, path: readonly ContainerKind[]): unknown => {
  let current = root

  for (const kind of path) {
    current = childAt(current, kind)
  }

  return current
}

const assertDeepAliases = (root: unknown, path: readonly ContainerKind[]): void => {
  let current = root

  for (const kind of path) {
    const child = childAt(current, kind)
    let aliasSet: Set<unknown>

    switch (kind) {
      case 'array':
        assert.equal((current as unknown[])[1], child)
        aliasSet = (current as unknown[])[2] as Set<unknown>
        break
      case 'map':
        assert.equal((current as Map<string, unknown>).get('alias'), child)
        aliasSet = (current as Map<string, unknown>).get('set') as Set<unknown>
        break
      case 'object':
        assert.equal((current as { alias: unknown }).alias, child)
        aliasSet = (current as { set: Set<unknown> }).set
        break
    }

    assert.equal(aliasSet.has(child), true)
    current = child
  }
}

const makeSpecial = (kind: SpecialKind, bytes: Uint8Array, time: number): object => {
  switch (kind) {
    case 'arrayBuffer':
      return cloneBufferFrom(bytes)
    case 'dataView':
      return new DataView(cloneBufferFrom(bytes))
    case 'date':
      return new Date(time)
    case 'typedArray':
      return new Uint8Array(cloneBufferFrom(bytes))
  }
}

const mutateSpecial = (value: object, kind: SpecialKind): void => {
  switch (kind) {
    case 'arrayBuffer': {
      const bytes = new Uint8Array(value as ArrayBuffer)
      bytes[0] = (bytes[0] + 1) % 256
      return
    }
    case 'dataView': {
      const view = value as DataView
      view.setUint8(0, (view.getUint8(0) + 1) % 256)
      return
    }
    case 'date': {
      const date = value as Date
      date.setTime(date.getTime() + 1)
      return
    }
    case 'typedArray': {
      const typed = value as Uint8Array
      typed[0] = (typed[0] + 1) % 256
    }
  }
}

describe('patch property semantics', () => {
  it('keeps no-op createPatch recipes on the original supported value', () => {
    fc.assert(
      fc.property(supportedValueArbitrary, (current) => {
        const before = normalize(current)
        const result = createPatch(current, (draft) => draft)

        assert.equal(result, current)
        assert.deepEqual(normalize(current), before)
      }),
    )
  })

  it('snapshot(createPatch(...)) detaches while preserving observable supported value shape', () => {
    fc.assert(
      fc.property(supportedValueArbitrary, (current) => {
        const next = createPatch(current, (draft) => draft)
        const detached = snapshot(next)

        assert.deepEqual(normalize(detached), normalize(current))

        if (current !== null && typeof current === 'object') {
          assert.notEqual(detached, current)
        }
      }),
    )
  })

  it('publishes plain-object writes without mutating untouched current graph', () => {
    fc.assert(
      fc.property(fc.integer(), fc.string(), (count, label) => {
        const shared = { count }
        const current = { label, left: shared, right: shared }
        const before = normalize(current)

        const result = createPatch(current, (draft) => {
          draft.left.count += 1
          return draft
        })

        assert.deepEqual(normalize(current), before)
        assert.notEqual(result, current)
        assert.equal(result.left, result.right)
        assert.equal(result.left.count, count + 1)
      }),
    )
  })

  it('preserves array holes, present undefined slots, order, and moved draft identities', () => {
    fc.assert(
      fc.property(fc.integer(), (count) => {
        const current: Array<{ count: number } | undefined> = [{ count }, undefined]
        current.length = 4
        const before = normalize(current)

        const result = createPatch(current, (draft) => {
          const first = draft[0]
          draft.push(first)
          draft[1] = undefined
          return draft
        })

        assert.deepEqual(normalize(current), before)
        assert.equal(1 in result, true)
        assert.equal(3 in result, false)
        assert.equal(result[0], result[4])
        assert.deepEqual(result[0], { count })
      }),
    )
  })

  it('preserves Map insertion order, present undefined values, and draft-originating keys', () => {
    fc.assert(
      fc.property(fc.integer(), fc.string({ maxLength: 8 }), (count, key) => {
        const objectKey = { count }
        const current = { key: objectKey, map: new Map<unknown, unknown>([[key, undefined]]) }
        const before = normalize(current)

        const result = createPatch(current, (draft) => {
          draft.key.count += 1
          draft.map.set(draft.key, { seen: draft.key })
          return draft
        })

        assert.deepEqual(normalize(current), before)
        assert.deepEqual(Array.from(result.map.keys()), [key, result.key])
        assert.equal(result.map.has(key), true)
        assert.equal(result.map.get(key), undefined)
        assert.equal((result.map.get(result.key) as { seen: { count: number } }).seen, result.key)
      }),
    )
  })

  it('preserves Set order, undefined membership, and draft-originating values', () => {
    fc.assert(
      fc.property(fc.integer(), (count) => {
        const item = { count }
        const current = { item, set: new Set<unknown>([undefined]) }
        const before = normalize(current)

        const result = createPatch(current, (draft) => {
          draft.item.count += 1
          draft.set.add(draft.item)
          return draft
        })

        assert.deepEqual(normalize(current), before)
        assert.deepEqual(Array.from(result.set), [undefined, result.item])
        assert.equal(result.set.has(result.item), true)
      }),
    )
  })

  it('isolates Date clone-on-read mutation and reuses unchanged Date reads', () => {
    fc.assert(
      fc.property(fc.integer({ max: 10_000, min: 0 }), (time) => {
        const current = { changed: new Date(time), unchanged: new Date(time) }
        const before = normalize(current)

        const result = createPatch(current, (draft) => {
          draft.changed.setTime(time + 1)
          draft.unchanged.getTime()
          return draft
        })

        assert.deepEqual(normalize(current), before)
        assert.notEqual(result.changed, current.changed)
        assert.equal(result.changed.getTime(), time + 1)
        assert.equal(result.unchanged, current.unchanged)
      }),
    )
  })

  it('isolates ArrayBuffer, DataView, and typed-array clone-on-read mutation with alias coherence', () => {
    fc.assert(
      fc.property(binaryArbitrary, (bytes) => {
        const buffer = cloneBufferFrom(bytes)
        const current = {
          buffer,
          typed: new Uint8Array(buffer),
          view: new DataView(buffer),
        }
        const before = normalize(current)
        const nextByte = (new Uint8Array(buffer)[0] + 1) % 256

        const result = createPatch(current, (draft) => {
          draft.typed[0] = nextByte
          draft.view.getUint8(0)
          return draft
        })

        assert.deepEqual(normalize(current), before)
        assert.notEqual(result.buffer, buffer)
        assert.equal(result.typed.buffer, result.buffer)
        assert.equal(result.view.buffer, result.buffer)
        assert.equal(new Uint8Array(result.buffer)[0], nextByte)
      }),
    )
  })

  it('preserves shared topology for ordinary mutations at generated depths', () => {
    fc.assert(
      fc.property(
        deepPathArbitrary,
        fc.integer(),
        fc.integer({ max: 100, min: 1 }),
        (path, count, delta) => {
          const leaf = { count }
          const current = buildDeepValue(path, leaf)
          const before = normalize(current)

          const result = createPatch(current, (draft) => {
            ;(navigateDeep(draft, path) as { count: number }).count += delta
            return draft
          })

          assert.deepEqual(normalize(current), before)
          assertDeepAliases(result, path)
          assert.equal((navigateDeep(result, path) as { count: number }).count, count + delta)
        },
      ),
    )
  })

  it('finalizes draft handles captured from generated depths inside ordinary returned roots', () => {
    fc.assert(
      fc.property(deepPathArbitrary, fc.integer(), (path, count) => {
        const current = buildDeepValue(path, { count })
        const before = normalize(current)

        const result = createPatch(current, (draft) => {
          const picked = navigateDeep(draft, path)
          ;(picked as { count: number }).count += 1
          return { picked, root: draft }
        })

        assert.deepEqual(normalize(current), before)
        assertDeepAliases(result.root, path)
        assert.equal(result.picked, navigateDeep(result.root, path))
        assert.deepEqual(result.picked, { count: count + 1 })
      }),
    )
  })

  it('preserves cycles that close from generated-depth leaves back to the root', () => {
    fc.assert(
      fc.property(deepPathArbitrary, fc.integer(), (path, count) => {
        const leaf: { count: number; root?: unknown } = { count }
        const current = buildDeepValue(path, leaf)
        leaf.root = current
        const before = normalize(current)

        const result = createPatch(current, (draft) => {
          ;(navigateDeep(draft, path) as { count: number }).count += 1
          return draft
        })
        const resultLeaf = navigateDeep(result, path) as { count: number; root?: unknown }

        assert.deepEqual(normalize(current), before)
        assertDeepAliases(result, path)
        assert.equal(resultLeaf.count, count + 1)
        assert.equal(resultLeaf.root, result)
      }),
    )
  })

  it('preserves clone-on-read isolation and alias topology at generated depths', () => {
    fc.assert(
      fc.property(
        deepPathArbitrary,
        specialKindArbitrary,
        binaryArbitrary,
        fc.integer({ max: 10_000, min: 0 }),
        (path, kind, bytes, time) => {
          const special = makeSpecial(kind, bytes, time)
          const current = buildDeepValue(path, special)
          const before = normalize(current)

          const result = createPatch(current, (draft) => {
            mutateSpecial(navigateDeep(draft, path) as object, kind)
            return draft
          })

          assert.deepEqual(normalize(current), before)
          assertDeepAliases(result, path)
          assert.notDeepEqual(normalize(navigateDeep(result, path)), normalize(special))
        },
      ),
    )
  })

  it('keeps patch publication observationally equivalent to reconcile(current, createPatch(current, recipe))', () => {
    fc.assert(
      fc.property(fc.integer(), fc.string({ maxLength: 8 }), (count, label) => {
        const currentForCreatePatch = { label, nested: { count } }
        const currentForPatch = { label, nested: { count } }

        const next = createPatch(currentForCreatePatch, (draft) => {
          draft.nested.count += 1
          return draft
        })
        const reconciled = reconcile(currentForCreatePatch, next)
        const patched = patch(currentForPatch, (draft) => {
          draft.nested.count += 1
          return draft
        })

        assert.deepEqual(normalize(patched), normalize(reconciled))
      }),
    )
  })
})
