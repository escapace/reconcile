import { assert, describe, it } from 'vitest'
import { createPatch, patch } from '../patch'
import { reconcile } from '../reconcile'
import { snapshot } from '../snapshot'

describe('Optimization Integrity', () => {
  it('preserves own-key order including Symbols and non-enumerable properties', () => {
    const sym = Symbol('test')

    interface Current {
      [key: symbol]: number
      '1': number
      '2': number
      'enumerable': number
      'non-enumerable': number
    }

    const current: Current = Object.create(null) as Current
    Object.defineProperty(current, 'enumerable', {
      configurable: true,
      enumerable: true,
      value: 1,
      writable: true,
    })
    Object.defineProperty(current, '2', {
      configurable: true,
      enumerable: true,
      value: 2,
      writable: true,
    })
    Object.defineProperty(current, '1', {
      configurable: true,
      enumerable: true,
      value: 1,
      writable: true,
    })
    Object.defineProperty(current, 'non-enumerable', {
      configurable: true,
      enumerable: false,
      value: 3,
      writable: true,
    })
    Object.defineProperty(current, sym, {
      configurable: true,
      enumerable: true,
      value: 4,
      writable: true,
    })

    const expectedOrder = Reflect.ownKeys(current)

    // Verify snapshot
    const snap = snapshot(current) as Current
    assert.deepEqual(Reflect.ownKeys(snap), expectedOrder)
    assert.equal(snap['non-enumerable'], 3)
    assert.equal(snap[sym], 4)

    // Verify patch/createPatch
    const result = patch(current, (draft: Current) => {
      draft.enumerable = 10
      return draft
    })
    assert.deepEqual(Reflect.ownKeys(result), expectedOrder)
    assert.equal(result.enumerable, 10)
    assert.equal(result['non-enumerable'], 3)
    assert.equal(result[sym], 4)

    // Verify reconcile
    const next = snapshot(current) as Current
    next.enumerable = 20
    const reconciled = reconcile(current, next)
    assert.deepEqual(Reflect.ownKeys(reconciled), expectedOrder)
  })

  it('correctly covers Symbols and non-data properties in finalization and reconciliation', () => {
    const sym1 = Symbol('sym1')
    const sym2 = Symbol('sym2')

    interface SymbolObject {
      [key: symbol]: { count: number }
    }
    const current: SymbolObject = { [sym1]: { count: 1 } }

    // Cover Symbols in valueRequiresFinalization and finalizePlainObject
    const result = createPatch(current, (draft: SymbolObject) => {
      draft[sym1].count = 2
      const fresh: SymbolObject = {}
      fresh[sym2] = draft[sym1]
      return fresh
    })

    assert.equal(result[sym2].count, 2)
    assert.notEqual(result[sym2], current[sym1])

    // Cover Symbols deletion in reconcile (empty-object fast path)
    const emptyResult = reconcile(current, {})
    assert.equal(Object.getOwnPropertySymbols(emptyResult).length, 0)

    // Cover non-data Symbol property in finalizePlainObject (line 1154)
    interface WithGetter {
      [key: symbol]: { count: number }
      other?: number
    }
    const currentWithGetter = Object.create(null) as WithGetter
    Object.defineProperty(currentWithGetter, sym1, {
      configurable: true,
      enumerable: true,
      get: () => ({ count: 1 }),
    })
    const resultWithGetter = createPatch(currentWithGetter, (draft: WithGetter) => {
      draft.other = 1 // Mutate to force finalizePlainObject
      return draft
    })
    assert.equal(resultWithGetter[sym1].count, 1)
    assert.equal(resultWithGetter.other, 1)

    // Cover mapKeySemanticallyUnchanged specialBase branch (line 882)
    const dateKey = new Date('2024-01-01T00:00:00.000Z')
    const currentWithMap: {
      dateKey: Date
      map: Map<Date, number>
      other?: number
    } = { dateKey, map: new Map([[dateKey, 1]]) }
    createPatch(currentWithMap, (draft: typeof currentWithMap) => {
      void draft.dateKey // Access but don't mutate
      draft.other = 1 // Mutate root to force finalization
      return draft
    })

    // Cover Proxy ownKeys trap (line 288)
    createPatch({ a: 1 }, (draft: { a: number }) => {
      assert.deepEqual(Reflect.ownKeys(draft), ['a'])
      return draft
    })

    // Cover sparse-array unmutated draft check (line 850)
    // eslint-disable-next-line no-sparse-arrays
    const sparse = [, , 1] as Array<number | undefined>
    createPatch(sparse, (draft: typeof sparse) => {
      void draft[2] // Access to create draft
      return { other: 1, sparse: draft }
    })
  })

  it('preserves non-enumerable data descriptors through plain-object finalization', () => {
    const hidden = { count: 1 }
    const current: {
      visible: number
      hidden?: { count: number }
    } = { visible: 0 }

    Object.defineProperty(current, 'hidden', {
      configurable: false,
      enumerable: false,
      value: hidden,
      writable: false,
    })

    const result = createPatch(current, (draft: typeof current) => {
      draft.visible = 2
      return draft
    })

    const descriptor = Object.getOwnPropertyDescriptor(result, 'hidden')
    assert.deepEqual(descriptor, {
      configurable: false,
      enumerable: false,
      value: hidden,
      writable: false,
    })
    assert.equal(result.hidden, hidden)
    assert.equal(result.visible, 2)
  })

  it('preserves non-enumerable drafted child descriptors and shared-image coherence', () => {
    const shared = { count: 0 }
    const current: {
      visible: { count: number }
      hidden?: { count: number }
      other?: number
    } = { visible: shared }

    Object.defineProperty(current, 'hidden', {
      configurable: true,
      enumerable: false,
      value: shared,
      writable: true,
    })

    const result = createPatch(current, (draft: typeof current) => {
      draft.visible.count = 2
      draft.other = 1
      return draft
    })

    const descriptor = Object.getOwnPropertyDescriptor(result, 'hidden')
    assert.deepEqual(descriptor, {
      configurable: true,
      enumerable: false,
      value: result.visible,
      writable: true,
    })
    assert.equal(result.hidden, result.visible)
    assert.notEqual(result.hidden, shared)
    assert.equal(result.hidden?.count, 2)
    assert.equal(result.other, 1)
  })

  it('preserves symbol-keyed non-enumerable drafted child descriptors through plain-object finalization', () => {
    const hidden = Symbol('hidden')
    const shared = { count: 0 }
    const current: {
      visible: { count: number }
      [hidden]?: { count: number }
      other?: number
    } = { visible: shared }

    Object.defineProperty(current, hidden, {
      configurable: true,
      enumerable: false,
      value: shared,
      writable: true,
    })

    const result = createPatch(current, (draft: typeof current) => {
      draft.visible.count = 3
      draft.other = 1
      return draft
    })

    const descriptor = Object.getOwnPropertyDescriptor(result, hidden)
    assert.deepEqual(descriptor, {
      configurable: true,
      enumerable: false,
      value: result.visible,
      writable: true,
    })
    assert.equal(result[hidden], result.visible)
    assert.notEqual(result[hidden], shared)
    assert.equal(result[hidden]?.count, 3)
    assert.equal(result.other, 1)
  })

  it('preserves prototype and untouched non-enumerable descriptors on the first plain-object copy', () => {
    const prototype = { inherited: 'from-prototype' }
    const current = Object.create(prototype) as {
      visible: number
      hidden?: { count: number }
    }

    Object.defineProperty(current, 'hidden', {
      configurable: true,
      enumerable: false,
      value: { count: 1 },
      writable: false,
    })
    current.visible = 1

    const result = createPatch(current, (draft: typeof current) => {
      draft.visible = 2
      return draft
    })

    assert.equal(Object.getPrototypeOf(result), prototype)
    assert.deepEqual(Object.getOwnPropertyDescriptor(result, 'hidden'), {
      configurable: true,
      enumerable: false,
      value: current.hidden,
      writable: false,
    })
    assert.equal(result.hidden, current.hidden)
    assert.equal(result.visible, 2)
    assert.equal(
      (Object.getPrototypeOf(result) as { inherited: string }).inherited,
      'from-prototype',
    )
  })

  it('preserves observable accessor-backed values on the first plain-object copy', () => {
    const current = {
      _count: 1,
      visible: 0,
      get count() {
        return this._count
      },
      set count(next: number) {
        this._count = next
      },
    }

    const result = createPatch(current, (draft) => {
      draft.visible = 2
      return draft
    })

    assert.equal(result.count, 1)
    result.count = 3
    assert.equal(result.count, 3)
    assert.equal(current.count, 1)
    assert.equal(result.visible, 2)
  })

  it('correctly discovers drafts hidden in fresh objects (containsDraft safety)', () => {
    const current = { a: { b: 1 } }
    const result = createPatch(current, (draft: typeof current) => {
      draft.a.b = 2
      return { nested: { target: draft.a } }
    })

    assert.notEqual(result.nested.target, current.a)
    assert.equal(result.nested.target.b, 2)
  })

  it('correctly handles unmutated but drafted subtrees (shortcut safety)', () => {
    const current = { a: { b: { c: 1 } }, d: 2 }
    const result = createPatch(current, (draft: typeof current) => {
      // Access but don't mutate a.b
      void draft.a.b.c
      draft.d = 3
      return draft
    })

    assert.equal(result.a, current.a) // Should be shared
    assert.equal(result.a.b, current.a.b) // Should be shared
    assert.equal(result.d, 3)
  })

  it('preserves Map key coherence with drafted keys', () => {
    const key = { id: 1 }
    const current = { key, map: new Map([[key, 'val']]) }
    const result = patch(current, (draft: typeof current) => {
      draft.key.id = 2
      return draft
    })

    const [resultKey] = Array.from(result.map.keys()) as [typeof key]
    assert.equal(resultKey, result.key)
    assert.equal(resultKey.id, 2)
  })

  it('materializes an unmodified sibling draft when a shared ordinary descendant changed elsewhere', () => {
    const shared = { count: 0 }
    const current = {
      left: { ref: shared },
      right: { ref: shared },
    }

    const result = createPatch(current, (draft: typeof current) => {
      draft.left.ref.count = 2
      void draft.right
      return {
        left: draft.left,
        right: draft.right,
      }
    })

    assert.notEqual(result.left, current.left)
    assert.notEqual(result.right, current.right)
    assert.equal(result.left.ref, result.right.ref)
    assert.notEqual(result.left.ref, shared)
    assert.equal(result.left.ref.count, 2)
  })

  it('materializes an unmodified sibling draft when a shared clone-on-read special changed elsewhere', () => {
    const sharedDate = new Date('2024-01-01T00:00:00.000Z')
    const current = {
      left: { ref: sharedDate },
      right: { ref: sharedDate },
    }

    const result = createPatch(current, (draft: typeof current) => {
      draft.left.ref.setUTCFullYear(2025)
      void draft.right
      return {
        left: draft.left,
        right: draft.right,
      }
    })

    assert.notEqual(result.left, current.left)
    assert.notEqual(result.right, current.right)
    assert.equal(result.left.ref, result.right.ref)
    assert.notEqual(result.left.ref, sharedDate)
    assert.equal(result.left.ref.getUTCFullYear(), 2025)
    assert.equal(sharedDate.getUTCFullYear(), 2024)
  })

  it('tolerates proxy plain-object keys whose descriptor lookup returns undefined during reflection and first copy', () => {
    const target = {
      child: { count: 0 },
      value: 1,
    }
    const current = new Proxy(target, {
      getOwnPropertyDescriptor(target_, property) {
        if (property === 'phantom') {
          return undefined
        }

        return Reflect.getOwnPropertyDescriptor(target_, property)
      },
      ownKeys(target_) {
        return ['phantom', ...Reflect.ownKeys(target_)]
      },
    }) as { phantom?: unknown } & typeof target

    const result = createPatch(current, (draft) => {
      assert.deepEqual(Reflect.ownKeys(draft), ['phantom', 'child', 'value'])
      assert.equal(Object.getOwnPropertyDescriptor(draft, 'phantom'), undefined)
      draft.value = 2
      return draft
    })

    assert.deepEqual(Reflect.ownKeys(result), ['child', 'value'])
    assert.equal(result.child, target.child)
    assert.equal(result.value, 2)
  })

  it('matches set members added as draft handles when probed through their base objects', () => {
    const current = {
      item: { count: 0 },
      set: new Set<object>(),
    }

    const result = createPatch(current, (draft: typeof current) => {
      draft.set.add(draft.item)
      assert.equal(draft.set.has(current.item), true)
      assert.equal(draft.set.delete(current.item), true)
      draft.set.add(draft.item)
      return draft
    })

    const [entry] = Array.from(result.set) as [typeof result.item]
    assert.equal(entry, result.item)
    assert.equal(result.set.has(result.item), true)
  })

  it('reuses a cached changed base materialization decision when both the base object and an unmodified draft handle are returned', () => {
    const shared = { count: 0 }
    const current = {
      left: { ref: shared },
      right: { ref: shared },
    }

    const result = createPatch(current, (draft: typeof current) => {
      draft.left.ref.count = 3
      void draft.right
      return {
        fromBase: current.right,
        fromDraft: draft.right,
      }
    })

    assert.notEqual(result.fromBase, current.right)
    assert.notEqual(result.fromDraft, current.right)
    assert.equal(result.fromBase, result.fromDraft)
    assert.equal(result.fromBase.ref.count, 3)
    assert.notEqual(result.fromBase.ref, shared)
  })

  it('checks an unmodified draft handle after its base object was already memoized unchanged', () => {
    const current = {
      child: { count: 0 },
      other: 1,
    }

    const result = createPatch(current, (draft: typeof current) => {
      void draft.child
      return {
        fromBase: current.child,
        fromDraft: draft.child,
      }
    })

    assert.equal(result.fromBase, current.child)
    assert.equal(result.fromBase.count, 0)
    assert.equal(result.fromDraft.count, 0)
  })

  it('reuses one draft proxy when the same plain object is reached through sibling properties', () => {
    const shared = { count: 0 }
    const current = {
      left: shared,
      right: shared,
    }

    const result = createPatch(current, (draft: typeof current) => {
      assert.equal(draft.left, draft.right)
      draft.left.count = 4
      return draft
    })

    assert.equal(result.left, result.right)
    assert.notEqual(result.left, shared)
    assert.equal(result.left.count, 4)
  })

  it('reuses one draft wrapper when the same map is reached through sibling properties', () => {
    const shared = new Map<string, { count: number }>([['item', { count: 0 }]])
    const current = {
      left: shared,
      right: shared,
    }

    const result = createPatch(current, (draft: typeof current) => {
      assert.equal(draft.left, draft.right)
      draft.left.get('item')!.count = 5
      return draft
    })

    assert.equal(result.left, result.right)
    assert.notEqual(result.left, shared)
    assert.equal(result.left.get('item')!.count, 5)
  })

  it('reuses one draft wrapper when the same set is reached through sibling properties', () => {
    const sharedItem = { count: 0 }
    const shared = new Set<object>([sharedItem])
    const current = {
      item: sharedItem,
      left: shared,
      right: shared,
    }

    const result = createPatch(current, (draft: typeof current) => {
      assert.equal(draft.left, draft.right)
      assert.equal(draft.left.has(draft.item), true)
      draft.item.count = 6
      return draft
    })

    assert.equal(result.left, result.right)
    assert.notEqual(result.left, shared)
    const [entry] = Array.from(result.left) as [typeof result.item]
    assert.equal(entry, result.item)
    assert.equal(entry.count, 6)
  })

  it('correctly handles shared references where only one path is drafted (shortcut safety)', () => {
    const b = { count: 1 }
    const current = { a: { b }, c: { b } }

    const result = patch(current, (draft: typeof current) => {
      draft.a.b.count = 2
      void draft.c // Access c to create a draft handle, but don't access c.b
      return draft
    })

    assert.equal(result.a.b.count, 2)
    assert.equal(result.c.b.count, 2)
    assert.equal(result.a.b, result.c.b) // Sharing MUST be preserved after publication
    assert.equal(result.a.b, b) // Sharing with current identity is preserved by reconcile
  })
})
