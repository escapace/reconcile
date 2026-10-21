import { assert, describe, it } from 'vitest'
import { isReconcileError, produce, reconcile, serialize, snapshot } from '../index'

// Copies keep the source's prototype, so an instance of a built-in subclass stays one in every
// function, as class instances and typed arrays already did. lean/Types/CopyPrototype.lean states the
// rule and check-copy-prototype-runtime.ts compares every kind natively. `deserialize` restores
// standard prototypes only, so `serialize` rejects every subclass (CopyPrototype.serializes).

class Link extends URL {}
class List extends Array<number> {}
class Query extends URLSearchParams {}
class Registry extends Map<string, number> {}
class Tags extends Set<string> {}
class Timestamp extends Date {}

const values = (): Array<[string, object]> => [
  ['Array', List.from([1])],
  ['Map', new Registry([['a', 1]])],
  ['Set', new Tags(['a'])],
  ['Date', new Timestamp(0)],
  ['URL', new Link('https://example.test/')],
  ['URLSearchParams', new Query('a=1')],
]

describe('copies keep built-in subclasses', () => {
  for (const [name, value] of values()) {
    it(`snapshot and reconcile keep a ${name} subclass`, () => {
      const copy = (snapshot({ value }) as { value: object }).value
      assert.notStrictEqual(copy, value)
      assert.strictEqual(Object.getPrototypeOf(copy), Object.getPrototypeOf(value))
      const holder: Record<string, unknown> = { value: 0 }
      reconcile(holder, { value })
      assert.strictEqual(Object.getPrototypeOf(holder.value), Object.getPrototypeOf(value))
    })
  }

  it('produce keeps the subclass of a changed collection and date', () => {
    const current = { list: List.from([1]), tags: new Tags(['a']), time: new Timestamp(0) }
    const result = produce(current, (draft) => {
      draft.list.push(2)
      draft.tags.add('b')
      draft.time.setTime(5)
      return draft
    })
    assert.instanceOf(result.list, List)
    assert.instanceOf(result.tags, Tags)
    assert.instanceOf(result.time, Timestamp)
    assert.deepEqual([...result.list], [1, 2])
    assert.equal(result.time.getTime(), 5)
  })

  it('updates an existing object in place and keeps its own prototype', () => {
    const current = { tags: new Set(['a']) }
    const kept = current.tags
    reconcile(current, { tags: new Tags(['b']) })
    assert.strictEqual(current.tags, kept)
    assert.strictEqual(Object.getPrototypeOf(current.tags), Set.prototype)
  })

  it('serialize rejects every subclass, arrays included, and arrays on another prototype', () => {
    const rejected = [
      ...values().map(([, value]) => value),
      Object.setPrototypeOf([1], Object.prototype) as object,
      Object.setPrototypeOf([1], null) as object,
    ]
    for (const value of rejected) {
      let cause: unknown
      try {
        serialize({ value })
      } catch (error) {
        cause = isReconcileError(error) ? error.cause : error
      }
      assert.deepEqual(cause, {
        reason: 'unsupported prototype',
        type: 'SerializeValueUnsupported',
      })
    }
  })
})
