import { assert, describe, it } from 'vitest'
import { deserialize, isReconcileError, produce, reconcile, serialize, snapshot } from '../index'
import { thrown } from './fixtures/thrown'

// reconcile writes a changed own property by assignment, so own setters run and own accessors
// are kept; it never writes or overrides accessors on the prototype. lean/Property/PropertyWrite.lean
// proves the single-key decision and scripts/check/bridges/property-write.ts compares it natively.

function storingAccessor(target: object, key: string, initial: unknown) {
  const log: unknown[] = []
  let stored = initial
  Object.defineProperty(target, key, {
    configurable: true,
    enumerable: true,
    get: () => stored,
    set: (value: unknown) => {
      log.push(value)
      stored = value
    },
  })
  return log
}

class Temperature {
  celsius = 0
  get rounded(): number {
    return this.celsius
  }
  set rounded(value: number) {
    this.celsius = Math.round(value)
  }
}

const rejected = (run: () => unknown): boolean => {
  const error = thrown(run)
  return isReconcileError(error) && error.cause.type === 'PublicationRejected'
}

describe('reconcile and accessors', () => {
  it('assigns a changed own accessor through its setter and keeps it', () => {
    const current: Record<string, unknown> = { other: 1 }
    const log = storingAccessor(current, 'value', 1)
    const descriptor = Object.getOwnPropertyDescriptor(current, 'value')
    assert.equal(reconcile(current, { other: 1, value: 2 }), current)
    assert.deepEqual(log, [2])
    assert.deepEqual(Object.getOwnPropertyDescriptor(current, 'value'), descriptor)
    assert.equal(current.value, 2)
  })

  it('does not call the setter of an unchanged own accessor', () => {
    const current = {}
    const log = storingAccessor(current, 'value', 1)
    reconcile(current, { value: 1 })
    assert.deepEqual(log, [])
  })

  it('keeps an own accessor in place while other keys reorder around it', () => {
    const current: Record<string, unknown> = { after: 0 }
    storingAccessor(current, 'value', 1)
    // eslint-disable-next-line perfectionist/sort-objects -- Key order is the tested contract.
    reconcile(current, { value: 2, after: 0 })
    assert.deepEqual(Object.keys(current), ['value', 'after'])
    assert.equal(typeof Object.getOwnPropertyDescriptor(current, 'value')?.get, 'function')
  })

  it('deletes an own accessor that next lacks without calling its setter', () => {
    const current: Record<string, unknown> = { other: 0 }
    const log = storingAccessor(current, 'value', 1)
    reconcile(current, { other: 0 })
    assert.deepEqual(Object.keys(current), ['other'])
    assert.deepEqual(log, [])
  })

  it('rejects a changed getter-only accessor before writing anything', () => {
    const current: Record<string, unknown> = { other: 0 }
    Object.defineProperty(current, 'value', { configurable: true, enumerable: true, get: () => 1 })
    assert.ok(rejected(() => reconcile(current, { other: 1, value: 2 })))
    assert.equal(current.other, 0)
    assert.equal(typeof Object.getOwnPropertyDescriptor(current, 'value')?.get, 'function')
  })

  it('rejects data that would override an accessor on the prototype, before writing', () => {
    const current = new Temperature()
    assert.ok(rejected(() => reconcile(current, { celsius: 1, rounded: 5 })))
    assert.equal(current.celsius, 0)
    assert.notOk(Object.hasOwn(current, 'rounded'))
  })

  it('writes data over own keys that shadow a prototype accessor, in or out of order', () => {
    // In order, the own key list answers which desired keys are own; out of order, each is asked.
    for (const next of [
      { celsius: 1, rounded: 5 },
      Object.fromEntries([
        ['rounded', 5],
        ['celsius', 1],
      ]) as { celsius: number; rounded: number },
    ]) {
      const current = new Temperature()
      Object.defineProperty(current, 'rounded', {
        configurable: true,
        enumerable: true,
        value: 0,
        writable: true,
      })
      const state = { current }
      reconcile(state, { current: next })
      assert.strictEqual(state.current, current)
      assert.deepEqual(Object.getOwnPropertyDescriptor(current, 'rounded')?.value, 5)
      assert.equal(current.celsius, 1)
    }
  })

  it('replaces such an object at a nested position, as other incompatible objects', () => {
    const temperature = new Temperature()
    const state = { temperature }
    reconcile(state, { temperature: { celsius: 1, rounded: 5 } })
    assert.notStrictEqual(state.temperature, temperature)
    assert.notOk(Object.hasOwn(temperature, 'rounded'))
  })

  it('applies data through a class setter with a produce recipe', () => {
    const current = new Temperature()
    reconcile(
      current,
      produce(current, (draft) => {
        draft.rounded = 5.4
        return draft
      }),
    )
    assert.equal(current.celsius, 5)
    assert.notOk(Object.hasOwn(current, 'rounded'))
  })

  it('reconciles a class instance with data of the same shape', () => {
    const current = new Temperature()
    const source = new Temperature()
    source.celsius = 7
    reconcile(current, snapshot(source) as Temperature)
    assert.equal(current.rounded, 7)
    assert.equal(Object.getPrototypeOf(current), Temperature.prototype)
  })

  it('defines a __proto__ key as an own data property without replacing the prototype', () => {
    const current = {}
    reconcile(current, JSON.parse('{"__proto__": 1}') as object)
    assert.equal(Object.getPrototypeOf(current), Object.prototype)
    assert.equal(Object.getOwnPropertyDescriptor(current, '__proto__')?.value, 1)
  })
})

describe('new objects hold data properties', () => {
  // A subclass field shadows the base class accessor of the same name.
  class Base {
    static calls = 0
    get value(): unknown {
      return 'base'
    }
    set value(_value: unknown) {
      Base.calls += 1
    }
  }
  class Shadowed extends Base {
    constructor() {
      super()
      Object.defineProperty(this, 'value', {
        configurable: true,
        enumerable: true,
        value: 1,
        writable: true,
      })
    }
  }

  it('copies an own property over a prototype accessor without running its setter', () => {
    Base.calls = 0
    const copy = snapshot(new Shadowed()) as Shadowed
    assert.equal(Object.getOwnPropertyDescriptor(copy, 'value')?.value, 1)
    assert.equal(Object.getPrototypeOf(copy), Shadowed.prototype)
    assert.equal(Base.calls, 0)
  })

  it('rebuilds such an object in produce without running the setter', () => {
    Base.calls = 0
    const result = produce(new Shadowed(), (draft) => {
      ;(draft as unknown as Record<string, unknown>).extra = 1
      return draft
    })
    assert.equal(Object.getOwnPropertyDescriptor(result, 'value')?.value, 1)
    assert.equal(Base.calls, 0)
  })

  it('adds such an object in reconcile without running the setter', () => {
    Base.calls = 0
    const state: Record<string, unknown> = { child: 0 }
    reconcile(state, { child: new Shadowed() })
    assert.equal(Object.getOwnPropertyDescriptor(state.child, 'value')?.value, 1)
    assert.equal(Base.calls, 0)
  })

  it('restores a __proto__ key as data without replacing the prototype', () => {
    const source = JSON.parse('{"__proto__": 1}') as object
    for (const copy of [
      snapshot(source) as object,
      deserialize(JSON.parse(JSON.stringify(serialize(source))), { maxBytes: 1024 }) as object,
    ]) {
      assert.equal(Object.getPrototypeOf(copy), Object.prototype)
      assert.equal(Object.getOwnPropertyDescriptor(copy, '__proto__')?.value, 1)
    }
  })
})
