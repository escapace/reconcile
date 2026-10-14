import { assert, it } from 'vitest'

import { produce } from '../index'

it.each([false, true])('isolates accessor traversal with a recipe read = %s', (read) => {
  const current = {
    count: 0,
    get next() {
      return ++this.count
    },
  }
  const result = produce(current, (draft) => {
    if (read) assert.equal(draft.next, 1)
    return draft
  })
  assert.equal(current.count, 0)
  assert.equal(result.count, read ? 2 : 1)
})

it.each([false, true])('isolates unread nested accessors with an unrelated write = %s', (write) => {
  const current = {
    child: {
      count: 0,
      get next() {
        return ++this.count
      },
    },
    flag: 0,
  }
  const result = produce(current, (draft) => {
    if (write) draft.flag = 1
    return draft
  })
  assert.equal(current.child.count, 0)
  assert.equal(current.flag, 0)
  assert.equal(result.flag, write ? 1 : 0)
})

it('isolates indexed accessor traversal', () => {
  const current = [0, 0]
  Object.defineProperty(current, '0', {
    configurable: true,
    enumerable: true,
    get(this: number[]) {
      return ++this[1]
    },
  })
  produce(current, (draft) => {
    assert.equal(draft[0], 1)
    return draft
  })
  assert.equal(current[1], 0)
})

it.each([false, true])(
  'publishes partial truncation after an error with a cached child = %s',
  (read) => {
    const current = [{ n: 0 }, { n: 1 }, { n: 2 }]
    Object.defineProperty(current, '1', { configurable: false })
    const result = produce(current, (draft) => {
      if (read) void draft[2]
      assert.throws(() => {
        draft.length = 0
      }, TypeError)
      assert.equal(draft.length, 2)
      assert.isFalse(2 in draft)
      assert.isUndefined(draft[2])
      return draft
    })
    assert.equal(result.length, 2)
    assert.isFalse(2 in result)
    assert.equal(result[0], current[0])
    assert.equal(result[1], current[1])
    assert.equal(current.length, 3)
    assert.equal(current[2].n, 2)
  },
)

it('preserves identity when rejected truncation makes no changes', () => {
  const current = [1]
  Object.defineProperty(current, '0', { configurable: false })
  const result = produce(current, (draft) => {
    assert.throws(() => {
      draft.length = 0
    }, TypeError)
    return draft
  })
  assert.equal(result, current)
})

it.each([false, true])('supports reflection on frozen inputs with array = %s', (array) => {
  const current = Object.freeze(array ? [{ n: 1 }] : { child: { n: 1 } })
  const key = array ? '0' : 'child'
  const result = produce(current, (draft) => {
    assert.deepEqual(Object.keys(draft), [key])
    const descriptors = Object.getOwnPropertyDescriptors(draft)
    assert.equal(descriptors[key].value, Reflect.get(draft, key))
    assert.notEqual(descriptors[key].value, Reflect.get(current, key))
    return draft
  })
  assert.equal(result, current)
})

it.each([false, true])(
  'preserves a cached child after rejected deletion with a child edit = %s',
  (edit) => {
    const current = { child: { n: 1 } }
    Object.defineProperty(current, 'child', { configurable: false })
    const result = produce(current, (draft) => {
      const held = draft.child
      if (edit) held.n = 2
      assert.isFalse(Reflect.deleteProperty(draft, 'child'))
      assert.equal(draft.child, held)
      return draft
    })
    assert.equal(result.child.n, edit ? 2 : 1)
    if (!edit) assert.equal(result, current)
    assert.equal(current.child.n, 1)
  },
)

it('preserves child sharing through an unchanged getter alias', () => {
  const current = {
    child: { n: 1 },
    get alias() {
      return this.child
    },
  }
  const result = produce(current, (draft) => draft)
  assert.equal(result.child, current.child)
  assert.equal(result.alias, current.child)
})
