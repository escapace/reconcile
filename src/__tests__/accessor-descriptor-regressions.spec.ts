import { assert, it } from 'vitest'
import { reactive } from 'vue'

import { produce } from '../index'

it.each([false, true])(
  'reevaluates object getters after replacing their dependency, reread = %s',
  (reread) => {
    const current = {
      child: { n: 1 },
      get alias() {
        return this.child
      },
    }
    const result = produce(current, (draft) => {
      const held = draft.alias
      draft.child = { n: 2 }
      if (reread) {
        assert.equal(draft.alias, draft.child)
        assert.notEqual(draft.alias, held)
        draft.alias.n = 3
      }
      return draft
    })
    assert.equal(result.alias, result.child)
    assert.equal(result.child.n, reread ? 3 : 2)
    assert.equal(current.child.n, 1)
  },
)

it('reevaluates getters that switch between objects and primitives', () => {
  const current = {
    child: { n: 1 },
    enabled: true,
    get alias() {
      return this.enabled ? this.child : undefined
    },
  }
  const result = produce(current, (draft) => {
    assert.equal(draft.alias, draft.child)
    draft.enabled = false
    assert.isUndefined(draft.alias)
    return draft
  })
  assert.isUndefined(result.alias)
  assert.isTrue(current.enabled)
})

it('finalizes computed getters using nested draft changes', () => {
  const current = {
    child: { n: 1 },
    get computed() {
      return { n: this.child.n }
    },
  }
  const result = produce(current, (draft) => {
    assert.notEqual(draft.computed, draft.computed)
    draft.child.n = 2
    return draft
  })
  assert.equal(result.computed.n, 2)
  assert.equal(current.child.n, 1)
})

it('tracks setter backing-property replacements after child reads', () => {
  const current = {
    child: { n: 1 },
    get alias() {
      return this.child
    },
    set alias(value) {
      this.child = value
    },
  }
  const result = produce(current, (draft) => {
    const held = draft.child
    draft.alias = { n: 2 }
    assert.notEqual(draft.child, held)
    assert.equal(draft.alias, draft.child)
    assert.equal(draft.child.n, 2)
    return draft
  })
  assert.equal(result.child.n, 2)
  assert.equal(result.alias, result.child)
  assert.equal(current.child.n, 1)
})

it('runs equal-value setters and isolates their nested mutations', () => {
  const current = {
    child: { n: 1 },
    get count() {
      return this.child.n
    },
    set count(value: number) {
      this.child.n = value + 1
    },
  }
  const result = produce(current, (draft) => {
    draft.count = 1
    assert.equal(draft.count, 2)
    return draft
  })
  assert.equal(result.count, 2)
  assert.equal(result.child.n, 2)
  assert.equal(current.child.n, 1)
})

it('discards setter mutations when the recipe returns current', () => {
  const current = {
    child: { n: 1 },
    get count() {
      return this.child.n
    },
    set count(value: number) {
      this.child.n = value
    },
  }
  const result = produce(current, (draft) => {
    draft.count = 2
    return current
  })
  assert.equal(result, current)
  assert.equal(current.child.n, 1)
})

it.each(['child', Symbol('child')])(
  'isolates mutations through a data descriptor for %s',
  (key) => {
    const current: Record<PropertyKey, { n: number }> = { [key]: { n: 1 } }
    const result = produce(current, (draft) => {
      const descriptor = Object.getOwnPropertyDescriptor(draft, key)!
      assert.notEqual(descriptor.value, current[key])
      assert.equal(descriptor.value, draft[key])
      ;(descriptor.value as { n: number }).n = 2
      return draft
    })
    assert.equal(result[key].n, 2)
    assert.equal(current[key].n, 1)
  },
)

it('isolates mutations through array element descriptors', () => {
  const current = [{ n: 1 }]
  const result = produce(current, (draft) => {
    const value = Object.getOwnPropertyDescriptor(draft, '0')!.value as { n: number }
    value.n = 2
    return draft
  })
  assert.equal(result[0].n, 2)
  assert.equal(current[0].n, 1)
})

it('isolates descriptor reads of special values and preserves shared buffers', () => {
  const buffer = new ArrayBuffer(4)
  const current = { buffer, date: new Date(0), view: new Uint8Array(buffer) }
  const result = produce(current, (draft) => {
    const descriptors = Object.getOwnPropertyDescriptors(draft)
    descriptors.date.value!.setTime(1)
    ;(descriptors.view.value as Uint8Array)[0] = 2
    return draft
  })
  assert.equal(result.date.getTime(), 1)
  assert.equal(result.view[0], 2)
  assert.equal(result.buffer, result.view.buffer)
  assert.equal(current.date.getTime(), 0)
  assert.equal(current.view[0], 0)
})

it('preserves structural sharing after read-only enumeration and descriptors', () => {
  const current = { child: { n: 1 }, other: { n: 2 } }
  const result = produce(current, (draft) => {
    assert.deepEqual(Object.keys(draft), ['child', 'other'])
    Object.getOwnPropertyDescriptors(draft)
    return draft
  })
  assert.equal(result, current)
})

it.each([['Vue', reactive]] as const)(
  'preserves wrapper identities through descriptor mutations for %s',
  (_name, wrap) => {
    const shared = { n: 1 }
    const current = wrap({ left: shared, right: shared })
    const result = produce(current, (draft) => {
      const value = Object.getOwnPropertyDescriptor(draft, 'left')!.value as { n: number }
      assert.equal(value, draft.right)
      value.n = 2
      return draft
    })
    assert.equal(result.left, result.right)
    assert.equal(result.left.n, 2)
    assert.equal(current.left.n, 1)
  },
)

it('uses the draft receiver for inherited accessors', () => {
  const prototype = {
    get alias(): { n: number } {
      return (this as unknown as { child: { n: number } }).child
    },
    set alias(value: { n: number }) {
      ;(this as unknown as { child: { n: number } }).child = value
    },
  }
  const current = Object.assign(Object.create(prototype) as typeof prototype, { child: { n: 1 } })
  const result = produce(current, (draft) => {
    const held = draft.alias
    draft.alias = { n: 2 }
    assert.notEqual(draft.alias, held)
    assert.equal(draft.alias, draft.child)
    return draft
  })
  assert.equal(result.child.n, 2)
  assert.equal(result.alias, result.child)
  assert.equal(current.child.n, 1)
})
