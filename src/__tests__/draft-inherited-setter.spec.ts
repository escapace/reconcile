import { describe, expect, it } from 'vitest'
import { isReconcileError } from '../index'
import { produce } from '../produce'
import { thrown } from './fixtures/thrown'

/** A prototype whose setter for `key` defines it on the receiver with `descriptor`, as the
 * setters of `node --frozen-intrinsics` and SES do with a data descriptor assignment would make. */
function definingPrototype(descriptor: (value: unknown) => PropertyDescriptor): object {
  return Object.defineProperty({}, 'key', {
    configurable: true,
    get: () => 'inherited',
    set(this: object, value: unknown) {
      Object.defineProperty(this, 'key', descriptor(value))
    },
  })
}

/** The error type a recipe makes `produce` throw. */
function thrownType(recipe: (draft: Record<string, unknown>) => void, base: object): unknown {
  const error = thrown(() =>
    produce(base as Record<string, unknown>, (draft) => {
      recipe(draft)
      return draft
    }),
  )
  return isReconcileError(error) ? error.cause.type : error
}

const assigned = (value: unknown): PropertyDescriptor => ({
  configurable: true,
  enumerable: true,
  value,
  writable: true,
})

const assign = (draft: Record<string, unknown>): void => {
  draft.key = 1
}

const define = (draft: Record<string, unknown>): void => {
  Object.defineProperty(draft, 'key', assigned(1))
}

describe('a recipe assignment through an inherited setter', () => {
  it('accepts the definition assignment would make, as on the object', () => {
    const prototype = definingPrototype(assigned)
    const object = Object.create(prototype) as Record<string, unknown>
    object.key = 1
    const result = produce(Object.create(prototype) as Record<string, unknown>, (draft) => {
      draft.key = 1
      return draft
    })
    expect(Object.getOwnPropertyDescriptor(result, 'key')).toEqual(
      Object.getOwnPropertyDescriptor(object, 'key'),
    )
    expect(Object.getPrototypeOf(result)).toBe(prototype)
  })

  it('refuses any other definition', () => {
    const prototype = definingPrototype((value) => ({ ...assigned(value), enumerable: false }))
    expect(thrownType(assign, Object.create(prototype) as object)).toBe(
      'DraftDefinePropertyUnsupported',
    )
  })

  it('refuses a definition of another key while the setter runs', () => {
    const prototype = Object.defineProperty({}, 'key', {
      configurable: true,
      get: () => undefined,
      set(this: object, value: unknown) {
        Object.defineProperty(this, 'other', assigned(value))
      },
    })
    expect(thrownType(assign, Object.create(prototype) as object)).toBe(
      'DraftDefinePropertyUnsupported',
    )
  })

  it('refuses a reflective definition outside a setter', () => {
    expect(thrownType(define, { key: 0 })).toBe('DraftDefinePropertyUnsupported')
  })
})
