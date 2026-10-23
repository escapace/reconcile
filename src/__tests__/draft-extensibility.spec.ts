import { describe, expect, it } from 'vitest'
import { produce } from '../index'

describe('drafts of non-extensible objects', () => {
  it.each<[string, <T extends object>(value: T) => T]>([
    ['frozen', Object.freeze],
    ['sealed', Object.seal],
    ['non-extensible', Object.preventExtensions],
  ])('refuse a new property of a %s object or array', (_name, lock) => {
    const object = lock({ a: 1 })
    const array = lock([1])
    produce({ array, object }, (draft) => {
      expect(Reflect.set(draft.object, 'b', 2)).toBe(false)
      expect(() => {
        ;(draft.object as Record<string, number>).b = 2
      }).toThrow(TypeError)
      expect(() => draft.array.push(2)).toThrow(TypeError)
      expect('b' in draft.object).toBe(false)
      expect(draft.array).toHaveLength(1)
    })
  })

  it('still write and delete what the object allows', () => {
    const sealed = Object.seal({ a: 1 })
    const closed = Object.preventExtensions({ a: 1, b: 2 })
    const result = produce({ closed, sealed }, (draft) => {
      draft.sealed.a = 2
      delete (draft.closed as Partial<typeof closed>).b
      return draft
    })
    expect(result.sealed).toEqual({ a: 2 })
    expect(result.closed).toEqual({ a: 1 })
  })
})

describe('extensibility and prototype changes on drafts', () => {
  it.each<[string, (value: object) => unknown]>([
    ['Object.freeze', Object.freeze],
    ['Object.seal', Object.seal],
    ['Object.preventExtensions', Object.preventExtensions],
    ['Object.setPrototypeOf', (value) => Object.setPrototypeOf(value, null) as unknown],
  ])('%s throws a TypeError on an object or array draft', (_name, change) => {
    const current = { array: [1], object: { a: 1 } }
    const result = produce(current, (draft) => {
      expect(() => change(draft.object)).toThrow(TypeError)
      expect(() => change(draft.array)).toThrow(TypeError)
      draft.object.a = 2
      draft.array.push(2)
      return draft
    })
    expect(result).toEqual({ array: [1, 2], object: { a: 2 } })
    expect(Object.isExtensible(result.object)).toBe(true)
    expect(Object.getPrototypeOf(result.object)).toBe(Object.prototype)
  })

  it('answers false from Reflect, and accepts the prototype the draft already has', () => {
    produce({ object: { a: 1 } }, (draft) => {
      expect(Reflect.preventExtensions(draft.object)).toBe(false)
      expect(Reflect.setPrototypeOf(draft.object, Array.prototype)).toBe(false)
      expect(Reflect.setPrototypeOf(draft.object, Object.prototype)).toBe(true)
      expect(Object.isExtensible(draft.object)).toBe(true)
    })
  })
})
