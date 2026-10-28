import assert from 'node:assert/strict'
import type { CapturedNode, Edge } from '../src/types'
import { OBJECT_KIND } from '../src/types/object'
import type { PropertySurface } from '../src/types/shared/property-publication'

export interface DeferredOrderCase {
  readonly current: object
  readonly name: string
  readonly node: CapturedNode
  readonly surface: PropertySurface<{ kind: symbol }>
  readonly failure?: Error
}

export const deferredKeys: PropertyKey[] = ['0', '2', 'a', 'b', Symbol('s'), Symbol('t')]

const modes = ['ordinary', 'fixed-late', 'sealed', 'unordered', 'incompatible'] as const
type Mode = (typeof modes)[number]

function capturedNode(properties: Map<PropertyKey, Edge>, keys: PropertyKey[]): CapturedNode {
  return {
    attributes: undefined,
    edges: [...properties.values()],
    keys,
    layout: { kind: OBJECT_KIND },
    observed: undefined,
    pinned: undefined,
    source: undefined,
  }
}

/** An ordered surface that accepts every receiver and reads keys natively. */
function nativeSurface(
  properties: Map<PropertyKey, Edge>,
  ordered: boolean,
): DeferredOrderCase['surface'] {
  return {
    desired: undefined,
    keys: Reflect.ownKeys,
    ordered,
    compatible: () => true,
    slots: () => properties,
  }
}

/** The masked keys in canonical order: integer keys ascending, then names and symbols reversed. */
function desiredOrder(mask: number): PropertyKey[] {
  const desired = deferredKeys.filter((_, index) => (mask & (1 << (index % 4))) !== 0)
  const numeric = desired.filter((key) => key === '0' || key === '2')
  const names = desired.filter((key) => typeof key === 'string' && key !== '0' && key !== '2')
  const symbols = desired.filter((key) => typeof key === 'symbol')
  return [...numeric, ...names.reverse(), ...symbols.reverse()]
}

/** The first `length` keys; `fixed-late` fixes the last one and `sealed` prevents extensions. */
function orderedBase(length: number, mode: Mode): object {
  const keys = deferredKeys.slice(0, length)
  const base = Object.fromEntries(keys.map((key) => [key, 1]))
  if (mode === 'fixed-late' && keys.length !== 0)
    Object.defineProperty(base, keys[keys.length - 1], {
      configurable: false,
      writable: false,
    })
  if (mode === 'sealed') Object.preventExtensions(base)
  return base
}

function orderedCase(length: number, mask: number, mode: Mode): DeferredOrderCase {
  const wanted = desiredOrder(mask)
  const current = orderedBase(length, mode)
  const properties = new Map<PropertyKey, Edge>(
    wanted.map((key) => [key, { node: undefined, value: 1 }]),
  )
  const surface: DeferredOrderCase['surface'] = {
    desired: undefined,
    ordered: mode !== 'unordered',
    compatible(_node, receiver) {
      assert.equal(receiver, current)
      return mode !== 'incompatible'
    },
    keys(receiver) {
      assert.equal(receiver, current)
      return Reflect.ownKeys(receiver)
    },
    slots() {
      return properties
    },
  }
  return {
    current,
    name: `${length}-${mask}-${mode}`,
    node: capturedNode(properties, wanted),
    surface,
  }
}

function arrayCase(extensible: boolean): DeferredOrderCase {
  const base: number[] = [1]
  base[2] = 1
  if (!extensible) Object.preventExtensions(base)
  const properties = new Map<PropertyKey, Edge>([
    ['0', { node: undefined, value: 1 }],
    ['2', { node: undefined, value: 1 }],
    ['length', { node: undefined, value: 3 }],
  ])
  return {
    current: base,
    name: `array-${extensible}`,
    node: capturedNode(properties, [...properties.keys()]),
    surface: nativeSurface(properties, false),
  }
}

/** Reading the descriptor of `a` fixes `b` and prevents extensions while preflight runs. */
function lateFixedCase(): DeferredOrderCase {
  const current = new Proxy(
    { a: 1, b: 1 },
    {
      getOwnPropertyDescriptor(target, key) {
        if (key === 'a') {
          Object.defineProperty(target, 'b', { configurable: false, writable: false })
          Object.preventExtensions(target)
        }
        return Reflect.getOwnPropertyDescriptor(target, key)
      },
    },
  )
  const properties = new Map<PropertyKey, Edge>([
    ['a', { node: undefined, value: 1 }],
    ['b', { node: undefined, value: 1 }],
  ])
  return {
    current,
    name: 'descriptor-mutates-late-fixed-and-extensibility',
    node: capturedNode(properties, ['b', 'a']),
    surface: nativeSurface(properties, true),
  }
}

/** The application error thrown at `boundary` must leave preflight with its identity intact. */
function throwingCase(boundary: string): DeferredOrderCase {
  const failure = new Error(`deferred-order:${boundary}`)
  const base = { a: 1, b: 1 }
  Object.defineProperty(base, 'b', { configurable: false, writable: false })
  const current = new Proxy(base, {
    get(target, key, receiver): unknown {
      if (boundary === 'get') throw failure
      return Reflect.get(target, key, receiver)
    },
    getOwnPropertyDescriptor(target, key) {
      if (boundary === 'descriptor' && key === 'b') throw failure
      return Reflect.getOwnPropertyDescriptor(target, key)
    },
    isExtensible(target) {
      if (boundary === 'extensible') throw failure
      return Reflect.isExtensible(target)
    },
  })
  // Removing a first key leaves the late fixed key retainable, so every error boundary is reached.
  const properties = new Map<PropertyKey, Edge>([['b', { node: undefined, value: 1 }]])
  return {
    current,
    failure,
    name: `throw-${boundary}`,
    node: capturedNode(properties, ['b']),
    surface: nativeSurface(properties, true),
  }
}

function orderedCases(run: (input: DeferredOrderCase) => void): void {
  for (let length = 0; length <= deferredKeys.length; length += 1)
    for (let mask = 0; mask < 16; mask += 1)
      for (const mode of modes) run(orderedCase(length, mask, mode))
}

export function deferredOrderCases(run: (input: DeferredOrderCase) => void): void {
  orderedCases(run)
  for (const extensible of [false, true]) run(arrayCase(extensible))
  run(lateFixedCase())
  for (const boundary of ['descriptor', 'get', 'extensible']) run(throwingCase(boundary))
}
