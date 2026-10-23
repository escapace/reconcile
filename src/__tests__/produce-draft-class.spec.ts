import { assert, describe, it } from 'vitest'
import { reactive } from 'vue'
import { produce } from '../index'

// A Map or Set draft is an instance of its source's class: its prototype chain is the draft's
// collection methods, then the source's chain. lean/Produce/DraftClass.lean proves the resolution rules
// and check-draft-class-runtime.ts compares them natively.

class Registry extends Map<string, number> {
  total(): number {
    let sum = 0
    for (const key of ['a', 'b']) sum += this.get(key) ?? 0
    return sum
  }
}

class Tags extends Set<string> {
  hasAll(...values: string[]): boolean {
    return values.every((value) => this.has(value))
  }
}

describe('Map and Set drafts are instances of their source class', () => {
  it('passes instanceof, toString and constructor checks', () => {
    produce({ map: new Map([['a', 1]]), set: new Set(['a']) }, (draft) => {
      assert.instanceOf(draft.map, Map)
      assert.instanceOf(draft.set, Set)
      assert.equal(Object.prototype.toString.call(draft.map), '[object Map]')
      assert.equal(Object.prototype.toString.call(draft.set), '[object Set]')
      assert.strictEqual(draft.map.constructor, Map)
      assert.strictEqual(draft.set.constructor, Set)
      return draft
    })
  })

  it('runs subclass methods on the draft through its collection methods', () => {
    const current = { registry: new Registry([['a', 1]]), tags: new Tags(['x']) }
    const result = produce(current, (draft) => {
      assert.instanceOf(draft.registry, Registry)
      assert.instanceOf(draft.tags, Tags)
      draft.registry.set('b', 2)
      draft.tags.add('y')
      assert.equal(draft.registry.total(), 3)
      assert.isTrue(draft.tags.hasAll('x', 'y'))
      return draft
    })
    assert.instanceOf(result.registry, Registry)
    assert.equal(result.registry.total(), 3)
    assert.equal(current.registry.total(), 1)
    assert.isTrue(result.tags.hasAll('x', 'y'))
  })

  // A draft's collection methods read the original, and then its working copy, with the
  // built-ins: a subclass's override of them never runs, as for every collection the library
  // reads. The result keeps the class, whose override then runs as usual.
  it('never calls a subclass override of a collection method on the original or the copy', () => {
    let calls = 0
    class Defaults extends Map<string, number> {
      override get(key: string): number | undefined {
        calls += 1
        return super.get(key) ?? 0
      }
    }
    const current = { value: new Defaults([['a', 1]]) }
    const result = produce(current, (draft) => {
      assert.equal(draft.value.get('missing'), undefined)
      draft.value.set('b', 2)
      assert.equal(draft.value.get('missing'), undefined)
      assert.equal(draft.value.get('b'), 2)
      return draft
    })
    assert.equal(calls, 0)
    assert.instanceOf(result.value, Defaults)
    assert.equal(result.value.get('missing'), 0)
    assert.isFalse(current.value.has('b'))
  })

  it('makes a Vue reactive Map draft an instance of Map', () => {
    const state = reactive({ map: new Map([['a', { n: 1 }]]) })
    produce(state, (draft) => {
      assert.instanceOf(draft.map, Map)
      return draft
    })
  })
})
