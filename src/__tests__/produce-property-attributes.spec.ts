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
