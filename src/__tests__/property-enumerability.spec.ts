import { assert, describe, it } from 'vitest'
import { isReconcileError, produce, reconcile, serialize, snapshot } from '../index'

// Enumerability is content: key listing, spread and JSON observe it, so a new object keeps its
// source's. Writability and configurability protect the source and are not copied into a
// snapshot or an object reconcile adds. An existing object keeps the attributes of its existing
// properties, and a produce draft follows its object's attributes. PropertyWrite.constructFrom states
// the rule for new objects and the property-construct bridge compares it natively.

const hidden = Symbol('hidden')

function source(): Record<PropertyKey, unknown> {
  const value: Record<PropertyKey, unknown> = { shown: 1 }
  Object.defineProperty(value, 'secret', {
    configurable: true,
    enumerable: false,
    value: 2,
    writable: true,
  })
  Object.defineProperty(value, hidden, {
    configurable: true,
    enumerable: false,
    value: 3,
    writable: true,
  })
  Object.defineProperty(value, 'fixed', {
    configurable: false,
    enumerable: true,
    value: 4,
    writable: false,
  })
  return value
}

const descriptor = (value: object, key: PropertyKey) => Object.getOwnPropertyDescriptor(value, key)

function assertCopied(copy: object): void {
  assert.deepEqual(Object.keys(copy), ['shown', 'fixed'])
  assert.deepEqual(descriptor(copy, 'secret'), {
    configurable: true,
    enumerable: false,
    value: 2,
    writable: true,
  })
  assert.deepEqual(descriptor(copy, hidden), {
    configurable: true,
    enumerable: false,
    value: 3,
    writable: true,
  })
  assert.deepEqual(descriptor(copy, 'fixed'), {
    configurable: true,
    enumerable: true,
    value: 4,
    writable: true,
  })
}

describe('new objects keep their source enumerability', () => {
  it('snapshot keeps hidden properties hidden', () => {
    assertCopied((snapshot({ value: source() }) as { value: object }).value)
    assertCopied(snapshot(Object.setPrototypeOf(source(), null) as object) as object)
  })

  it('an object reconcile adds keeps hidden properties hidden', () => {
    const holder: Record<string, unknown> = { value: 0 }
    reconcile(holder, { value: source() })
    assertCopied(holder.value as object)
  })

  it('a property reconcile adds to an existing object takes next enumerability', () => {
    const current: Record<PropertyKey, unknown> = { shown: 1 }
    reconcile(current, source())
    assert.deepEqual(Object.keys(current), ['shown', 'fixed'])
    assert.isFalse(descriptor(current, 'secret')!.enumerable)
  })

  it('an existing property kept in place keeps its own attributes', () => {
    // Already in next's order, so reconcile assigns it instead of recreating it.
    const current: Record<PropertyKey, unknown> = {}
    current.shown = 0
    current.secret = 0
    reconcile(current, source())
    assert.isTrue(descriptor(current, 'secret')!.enumerable)
    assert.equal(current.secret, 2)
  })

  it('produce keeps a hidden property hidden in a changed object', () => {
    const result = produce({ value: source() }, (draft) => {
      draft.value.shown = 5
      return draft
    })
    assert.deepEqual(Object.keys(result.value), ['shown', 'fixed'])
    assert.isFalse(descriptor(result.value, 'secret')!.enumerable)
  })

  it('serialize rejects a hidden property instead of revealing it', () => {
    let cause: unknown
    try {
      serialize({ value: source() })
    } catch (error) {
      cause = isReconcileError(error) ? error.cause : error
    }
    assert.deepEqual(cause, {
      reason: 'non-enumerable property',
      type: 'SerializeValueUnsupported',
    })
  })

  it('a produce draft follows its object attributes, so frozen state needs a snapshot', () => {
    const state: { count: number } = Object.freeze({ count: 0 })
    assert.throws(
      () =>
        produce(state, (draft) => {
          draft.count = 1
          return draft
        }),
      TypeError,
    )
    const result = produce(snapshot(state) as { count: number }, (draft) => {
      draft.count = 1
      return draft
    })
    assert.equal(result.count, 1)
  })
})
