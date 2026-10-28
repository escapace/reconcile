import { expect, it } from 'vitest'
import {
  canPublishProperties,
  PropertyOrder,
  propertySlots,
} from '../types/shared/property-publication'

it.each([false, true])(
  'preserves fixed and nonextensible observation order (ordered=%s)',
  (ordered) => {
    const events: string[] = []
    const target = Object.preventExtensions(Object.defineProperty({}, 'a', { value: 1 }))
    const current = new Proxy(target, {
      get(object, key, receiver) {
        events.push(`get:${String(key)}`)
        return Reflect.get(object, key, receiver) as unknown
      },
      getOwnPropertyDescriptor(object, key) {
        events.push(`descriptor:${String(key)}`)
        return Reflect.getOwnPropertyDescriptor(object, key)
      },
      isExtensible(object) {
        events.push('extensible')
        return Reflect.isExtensible(object)
      },
      ownKeys(object) {
        events.push('keys')
        return Reflect.ownKeys(object)
      },
    })
    const node = {
      attributes: undefined,
      edges: [{ node: undefined, value: 1 }],
      keys: ['a'],
      layout: { kind: Symbol('surface') },
      observed: undefined,
      pinned: undefined,
      source: undefined,
    }
    expect(
      canPublishProperties(
        node,
        current,
        {
          desired: undefined,
          keys: Reflect.ownKeys,
          ordered,
          slots: propertySlots,
          compatible: () => {
            events.push('compatible')
            return true
          },
        },
        [],
      ),
    ).toBe(true)
    expect(events).toEqual([
      'keys',
      'compatible',
      'descriptor:a',
      'get:a',
      'extensible',
      'descriptor:a',
    ])
  },
)

it('normalizes once across misses and preserves readiness across other sectors', () => {
  const order = new PropertyOrder(
    new Map(['1', 'kept', '2', 'next'].map((key) => [key, { node: undefined, value: 0 }])),
  )
  expect(order.keep('missing')).toBe(false)
  expect(Reflect.get(order, 'cursor')).toBe(1)
  expect(Reflect.get(order, 'stale')).toBe(false)
  expect(order.keep('missing')).toBe(false)
  expect(order.keep(Symbol('missing'))).toBe(false)
  expect(order.keep('0')).toBe(false)
  expect(order.keep('1')).toBe(true)
  expect(Reflect.get(order, 'stale')).toBe(false)
  expect(order.keep('kept')).toBe(true)
  expect(Reflect.get(order, 'stale')).toBe(true)
  expect(order.keep('next')).toBe(true)
  expect(Reflect.get(order, 'cursor')).toBe(4)
  expect(order.keep('missing')).toBe(false)
  expect(order.keep('missing')).toBe(false)
  expect(Reflect.get(order, 'stale')).toBe(false)
  expect(order.retained).toBe(3)
})

it('does not prepare an unused numeric-only name cursor', () => {
  const order = new PropertyOrder(
    new Map(['0', '1'].map((key) => [key, { node: undefined, value: 0 }])),
  )
  expect(order.keep('1')).toBe(true)
  expect(order.keep('0')).toBe(true)
  expect(Reflect.get(order, 'cursor')).toBe(0)
  expect(Reflect.get(order, 'stale')).toBe(true)
  expect(order.retained).toBe(2)
})

it('keeps symbol progress independent from exhausted and empty name cursors', () => {
  const first = Symbol('first')
  const second = Symbol('second')
  const order = new PropertyOrder(
    new Map<PropertyKey, { node: undefined; value: number }>([
      ['name', { node: undefined, value: 0 }],
      [first, { node: undefined, value: 0 }],
      [second, { node: undefined, value: 0 }],
    ]),
  )
  expect(order.keep('name')).toBe(true)
  expect(order.keep('missing')).toBe(false)
  expect(order.keep(second)).toBe(false)
  expect(order.keep(first)).toBe(true)
  expect(order.keep(second)).toBe(true)
  expect(order.keep(first)).toBe(false)
  expect(order.retained).toBe(3)
  const empty = new PropertyOrder(new Map())
  expect(empty.keep('missing')).toBe(false)
  expect(empty.keep(first)).toBe(false)
  expect(empty.keep('0')).toBe(false)
  expect(empty.retained).toBe(0)
})
