import assert from 'node:assert/strict'
import type { CapturedNode, Edge } from '../src/types'
import { OBJECT_KIND } from '../src/types/object'
import type { PropertySurface } from '../src/types/shared/property-publication'

export interface DeferredOrderCase {
  readonly current: object
  readonly events: string[]
  readonly name: string
  readonly node: CapturedNode
  readonly properties: Map<PropertyKey, Edge>
  readonly surface: PropertySurface<{ kind: symbol }>
  readonly failure?: Error
}

// fallow-ignore-next-line unused-export -- read by the run module that check-deferred-order-runtime.ts generates as source text
export const deferredKeys: PropertyKey[] = ['0', '2', 'a', 'b', Symbol('s'), Symbol('t')]

const modes = ['ordinary', 'fixed-late', 'sealed', 'unordered', 'incompatible'] as const
type Mode = (typeof modes)[number]

const label = (key: PropertyKey): string => String(deferredKeys.indexOf(key))

function capturedNode(properties: Map<PropertyKey, Edge>, keys: PropertyKey[]): CapturedNode {
  return { edges: [...properties.values()], keys, layout: { kind: OBJECT_KIND } }
}

/** An ordered surface that accepts every receiver and reads keys natively. */
function nativeSurface(
  properties: Map<PropertyKey, Edge>,
  ordered: boolean,
): DeferredOrderCase['surface'] {
  return {
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

function recordingHandler(events: string[]): ProxyHandler<object> {
  return {
    get(target, key, receiver): unknown {
      events.push(`get:${label(key)}`)
      return Reflect.get(target, key, receiver)
    },
    getOwnPropertyDescriptor(target, key) {
      events.push(`descriptor:${label(key)}`)
      return Reflect.getOwnPropertyDescriptor(target, key)
    },
    isExtensible(target) {
      events.push('extensible')
      return Reflect.isExtensible(target)
    },
    ownKeys(target) {
      events.push('keys')
      return Reflect.ownKeys(target)
    },
  }
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
  const events: string[] = []
  const current = new Proxy(orderedBase(length, mode), recordingHandler(events))
  const properties = new Map<PropertyKey, Edge>(wanted.map((key) => [key, { value: 1 }]))
  const surface: DeferredOrderCase['surface'] = {
    ordered: mode !== 'unordered',
    compatible(_node, receiver) {
      assert.equal(receiver, current)
      events.push('compatible')
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
    events,
    name: `${length}-${mask}-${mode}`,
    node: capturedNode(properties, wanted),
    properties,
    surface,
  }
}

function arrayCase(extensible: boolean): DeferredOrderCase {
  const base: number[] = [1]
  base[2] = 1
  if (!extensible) Object.preventExtensions(base)
  const events: string[] = []
  const current = new Proxy(base, {
    getOwnPropertyDescriptor(target, key) {
      events.push(`descriptor:${String(key)}`)
      return Reflect.getOwnPropertyDescriptor(target, key)
    },
    isExtensible(target) {
      events.push('extensible')
      return Reflect.isExtensible(target)
    },
  })
  const properties = new Map<PropertyKey, Edge>([
    ['0', { value: 1 }],
    ['2', { value: 1 }],
    ['length', { value: 3 }],
  ])
  return {
    current,
    events,
    name: `array-${extensible}`,
    node: capturedNode(properties, [...properties.keys()]),
    properties,
    surface: nativeSurface(properties, false),
  }
}

/** Reading the descriptor of `a` fixes `b` and prevents extensions while preflight runs. */
function lateFixedCase(): DeferredOrderCase {
  const base = { a: 1, b: 1 }
  const events: string[] = []
  const current = new Proxy(base, {
    get(target, key, receiver): unknown {
      events.push(`get:${String(key)}`)
      return Reflect.get(target, key, receiver)
    },
    getOwnPropertyDescriptor(target, key) {
      events.push(`descriptor:${String(key)}`)
      if (key === 'a') {
        Object.defineProperty(target, 'b', { configurable: false, writable: false })
        Object.preventExtensions(target)
        events.push('fixed-b-and-nonextensible')
      }
      return Reflect.getOwnPropertyDescriptor(target, key)
    },
    isExtensible(target) {
      events.push('extensible')
      return Reflect.isExtensible(target)
    },
  })
  const properties = new Map<PropertyKey, Edge>([
    ['a', { value: 1 }],
    ['b', { value: 1 }],
  ])
  return {
    current,
    events,
    name: 'descriptor-mutates-late-fixed-and-extensibility',
    node: capturedNode(properties, ['b', 'a']),
    properties,
    surface: nativeSurface(properties, true),
  }
}

/** The application error thrown at `boundary` must leave preflight with its identity intact. */
function throwingCase(boundary: string): DeferredOrderCase {
  const failure = new Error(`deferred-order:${boundary}`)
  const events: string[] = []
  const base = { a: 1, b: 1 }
  Object.defineProperty(base, 'b', { configurable: false, writable: false })
  const current = new Proxy(base, {
    get(target, key, receiver): unknown {
      events.push(`get:${String(key)}`)
      if (boundary === 'get') throw failure
      return Reflect.get(target, key, receiver)
    },
    getOwnPropertyDescriptor(target, key) {
      events.push(`descriptor:${String(key)}`)
      if (boundary === 'descriptor' && key === 'b') throw failure
      return Reflect.getOwnPropertyDescriptor(target, key)
    },
    isExtensible(target) {
      events.push('extensible')
      if (boundary === 'extensible') throw failure
      return Reflect.isExtensible(target)
    },
  })
  // Removing a first key leaves the late fixed key retainable, so every error boundary is reached.
  const properties = new Map<PropertyKey, Edge>([['b', { value: 1 }]])
  return {
    current,
    events,
    failure,
    name: `throw-${boundary}`,
    node: capturedNode(properties, ['b']),
    properties,
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
