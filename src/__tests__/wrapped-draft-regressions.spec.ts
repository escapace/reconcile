import { assert, describe, it } from 'vitest'
import { reactive, ref } from 'vue'

import { produce, reconcile } from '../index'

const identity = <T extends object>(value: T): T => value

describe.each([
  ['plain', identity],
  ['Vue', reactive],
] as const)('%s draft identities', (_name, wrap) => {
  it.each([false, true])('preserves unread aliases with parent write = %s', (writeParent) => {
    const shared = { value: 0 }
    const current = wrap({ flag: 0, left: shared, right: shared })
    const result = produce(current, (draft) => {
      draft.left.value = 1
      if (writeParent) draft.flag = 1
      return draft
    })

    assert.equal(result.left, result.right)
    assert.equal(result.right.value, 1)
    assert.equal(current.left.value, 0)
    assert.equal(current.flag, 0)
  })

  it('keeps a child handle stable across parent writes', () => {
    const shared = { value: 0 }
    const current = wrap({ flag: 0, left: shared, right: shared })
    const result = produce(current, (draft) => {
      const held = draft.left
      draft.flag = 1
      assert.equal(held, draft.right)
      draft.right.value = 2
      assert.equal(held.value, 2)
      return draft
    })

    assert.equal(result.left, result.right)
    assert.equal(result.left.value, 2)
    assert.equal(current.left.value, 0)
  })

  it('preserves a root cycle after a write', () => {
    const raw: { value: number; self?: unknown } = { value: 0 }
    raw.self = raw
    const current = wrap(raw)
    const result = produce(current, (draft) => {
      draft.value = 1
      return draft
    })

    assert.equal(result.self, result)
    assert.equal(result.value, 1)
    assert.equal(current.self, current)
    assert.equal(current.value, 0)
  })

  it('preserves descriptor attributes on an unread symbol alias', () => {
    const key = Symbol('alias')
    const shared = { value: 0 }
    const raw = { [key]: shared, left: shared }
    Object.defineProperty(raw, key, { enumerable: false, writable: false })
    const current = wrap(raw)
    const result = produce(current, (draft) => {
      draft.left.value = 1
      return draft
    })

    assert.equal(result[key], result.left)
    assert.equal(result[key].value, 1)
    assert.deepEqual(Object.getOwnPropertyDescriptor(result, key), {
      configurable: true,
      enumerable: false,
      value: result.left,
      writable: false,
    })
    assert.equal(current.left.value, 0)
  })

  it('preserves shared children when applying a caller publication', () => {
    const shared = { value: 0 }
    const current = wrap({ left: shared, right: shared })
    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.left.value = 3
        return draft
      }),
    )

    assert.equal(result.left, result.right)
    assert.equal(result.right.value, 3)
  })
})

describe('Vue collection copies', () => {
  it('deletes a wrapped set member using its draft handle', () => {
    const node = { value: 0 }
    const current = reactive({ node, set: new Set([node]) })
    const result = produce(current, (draft) => {
      assert.isTrue(draft.set.has(draft.node))
      assert.isTrue(draft.set.delete(draft.node))
      assert.equal(draft.set.size, 0)
      return draft
    })
    assert.equal(result.set.size, 0)
    assert.equal(current.set.size, 1)
  })

  it.each(['delete', 'set'] as const)('resolves map keys on copy for %s', (operation) => {
    const node = { value: 0 }
    const current = reactive({ map: new Map([[node, 1]]), node })
    const result = produce(current, (draft) => {
      assert.equal(draft.map.get(draft.node), 1)
      if (operation === 'delete') {
        assert.isTrue(draft.map.delete(draft.node))
        assert.equal(draft.map.size, 0)
      } else {
        draft.map.set(draft.node, 2)
        assert.equal(draft.map.size, 1)
        assert.equal(draft.map.get(draft.node), 2)
      }
      return draft
    })
    assert.equal(result.map.size, operation === 'delete' ? 0 : 1)
    assert.equal(result.map.get(result.node), operation === 'delete' ? undefined : 2)
    assert.equal(current.map.get(current.node), 1)
  })
})

it.each([false, true])(
  'preserves Vue unwrapped scalar values with parent write = %s',
  (writeParent) => {
    const current = reactive({ child: { value: 0 }, flag: 0, scalar: ref(7) })
    const result = produce(current, (draft) => {
      draft.child.value = 1
      if (writeParent) draft.flag = 1
      assert.equal(draft.scalar, 7)
      return draft
    })

    assert.equal(result.scalar, 7)
    assert.equal(current.child.value, 0)
  },
)
