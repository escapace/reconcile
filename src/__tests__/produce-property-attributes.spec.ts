import { assert, it } from 'vitest'

import { produce } from '../index'
import { attributeConfigurations } from './fixtures/public-api-fuzz'

interface Attributes {
  configurable: boolean
  enumerable: boolean
  writable: boolean
}

interface Leaf {
  value: number
}

// A property deleted and assigned again is an ordinary one, as in JavaScript, so its object is new
// even when the value is the same.
it('makes a new object when a recipe deletes and reassigns a property with other attributes', () => {
  for (const attributes of attributeConfigurations()) {
    if (!attributes.configurable) continue
    for (const key of ['c', Symbol('c')]) {
      const current: Record<PropertyKey, unknown> = {}
      Object.defineProperty(current, key, { ...attributes, value: 1 })
      const result = produce(current, (draft) => {
        delete draft[key]
        draft[key] = 1
        return draft
      })
      const plain = attributes.enumerable && attributes.writable
      assert.strictEqual(result === current, plain)
      assert.deepEqual(Object.getOwnPropertyDescriptor(result, key), {
        configurable: true,
        enumerable: true,
        value: 1,
        writable: true,
      })
    }
  }
})

it('makes a new array when a recipe deletes and reassigns an element with other attributes', () => {
  for (const attributes of attributeConfigurations()) {
    if (!attributes.configurable) continue
    const current = [0, 1]
    Object.defineProperty(current, 1, { ...attributes, value: 1 })
    const result = produce(current, (draft) => {
      Reflect.deleteProperty(draft, 1)
      draft[1] = 1
      return draft
    })
    assert.strictEqual(result === current, attributes.enumerable && attributes.writable)
    assert.deepEqual(Object.getOwnPropertyDescriptor(result, 1), {
      configurable: true,
      enumerable: true,
      value: 1,
      writable: true,
    })
  }
})

it('preserves native data attributes across cyclic publication and held-draft writes', () => {
  const configurations: Attributes[] = attributeConfigurations()

  for (const prototype of [null, Object.prototype]) {
    for (const key of ['left', '__proto__', Symbol('left')]) {
      for (const left of configurations) {
        for (const right of configurations) {
          checkAttributeCase(prototype, key, left, right)
        }
      }
    }
  }
})

function checkAttributeCase(
  prototype: object | null,
  key: PropertyKey,
  left: Attributes,
  right: Attributes,
): void {
  const leaf: Leaf = { value: 0 }
  const current = Object.create(prototype) as Record<PropertyKey, unknown>
  const self = { configurable: false, enumerable: false, writable: false }
  Object.defineProperty(current, key, { ...left, value: leaf })
  Object.defineProperty(current, 'right', { ...right, value: leaf })
  Object.defineProperty(current, 'self', { ...self, value: current })
  let held: typeof current | undefined
  const result = produce(current, (draft) => {
    held = draft
    ;(draft[key] as Leaf).value = 1
    return draft
  })

  assert.notStrictEqual(result, current)
  assert.strictEqual(Object.getPrototypeOf(result), prototype)
  assert.strictEqual(result[key], result.right)
  assert.strictEqual(result.self, result)
  assert.strictEqual((result[key] as Leaf).value, 1)
  assert.strictEqual(leaf.value, 0)
  const properties: Array<readonly [PropertyKey, Attributes]> = [
    [key, left],
    ['right', right],
    ['self', self],
  ]
  for (const [property, expected] of properties) {
    const actual = Object.getOwnPropertyDescriptor(result, property)!
    assert.deepEqual(
      {
        configurable: actual.configurable,
        enumerable: actual.enumerable,
        writable: actual.writable,
      },
      expected,
    )
    assert.strictEqual(actual.value, result[property])
  }

  ;(result[key] as Leaf).value = 2
  assert.strictEqual((held![key] as Leaf).value, 1)
  ;(held![key] as Leaf).value = 3
  assert.strictEqual((result[key] as Leaf).value, 2)
  assert.strictEqual(leaf.value, 0)
}
