import { assert, describe, it, vi } from 'vitest'
import { isReactive, isRef, markRaw, reactive, readonly, ref, shallowRef, toRaw, watch } from 'vue'

import { deserialize, isReconcileError, produce, reconcile, serialize, snapshot } from '../index'
import { encodeText } from './fixtures/text-codec'

const sync = { flush: 'sync' } as const

/** The type of the ReconcileError that `run` throws. */
function errorType(run: () => unknown): string {
  try {
    run()
  } catch (error) {
    assert.ok(isReconcileError(error))
    return error.cause.type
  }
  assert.fail('expected a ReconcileError')
}

it('reconciles the value of a ref in place, keeping its nested proxies', () => {
  const state = ref({ items: [] as Array<{ id: number }>, user: { name: 'Ada', role: 'admin' } })
  const user = state.value.user
  let name = 0
  let role = 0
  watch(
    () => state.value.user.name,
    () => name++,
    sync,
  )
  watch(
    () => state.value.user.role,
    () => role++,
    sync,
  )
  reconcile(state.value, { items: [{ id: 1 }], user: { name: 'Grace', role: 'admin' } })
  assert.equal(state.value.user, user)
  assert.deepEqual([name, role], [1, 0])
  // An added object is deeply reactive like any other mutation.
  assert.isTrue(isReactive(state.value.items[0]))
})

it('needs a new value to trigger a shallow ref', () => {
  const state = shallowRef({ user: { name: 'Ada' } })
  let triggered = 0
  watch(
    () => state.value.user.name,
    () => triggered++,
    sync,
  )
  reconcile(state.value, { user: { name: 'Grace' } })
  assert.equal(state.value.user.name, 'Grace')
  assert.equal(triggered, 0)
  state.value = produce(state.value, (draft) => {
    draft.user.name = 'Lin'
    return draft
  })
  assert.equal(triggered, 1)
})

it('writes through a ref that is a property of a reactive object', () => {
  const count = ref(1)
  const store = reactive({ count })
  reconcile(store, { count: 2 })
  assert.equal(count.value, 2)
  assert.isTrue(isRef(toRaw(store).count))
})

it('triggers nothing through the original object and rejects a readonly proxy', () => {
  const original = { user: { name: 'Ada' } }
  const proxy = reactive(original)
  let triggered = 0
  watch(
    () => proxy.user.name,
    () => triggered++,
    sync,
  )
  reconcile(original, { user: { name: 'Grace' } })
  assert.equal(proxy.user.name, 'Grace')
  assert.equal(triggered, 0)
  const warn = vi.spyOn(console, 'warn').mockImplementation(() => undefined)
  try {
    assert.equal(
      errorType(() => reconcile(readonly(original), { user: { name: 'Lin' } })),
      'PublicationRejected',
    )
  } finally {
    warn.mockRestore()
  }
})

it('rejects a ref object in stringify, as a class instance', () => {
  assert.equal(
    errorType(() => encodeText(ref({ a: 1 }))),
    'SerializeValueUnsupported',
  )
})

describe('markRaw objects', () => {
  it('stay in place and raw when next lacks the marker', () => {
    const raw = markRaw({ n: 1 })
    const state = reactive({ raw })
    reconcile(state, { raw: { n: 2 } })
    assert.equal(state.raw, raw)
    assert.isFalse(isReactive(state.raw))
    assert.equal(raw.n, 2)
    assert.equal(Object.getOwnPropertyDescriptor(raw, '__v_skip')?.value, true)
  })

  it('are not created from a kept object when next is marked, and stay marked when added', () => {
    const state = reactive({ added: [] as Array<{ v: number }>, kept: { v: 1 } })
    const kept = state.kept
    reconcile(state, { added: [markRaw({ v: 3 })], kept: markRaw({ v: 2 }) })
    assert.equal(state.kept, kept)
    assert.isTrue(isReactive(state.kept))
    assert.equal(state.kept.v, 2)
    assert.isFalse(isReactive(state.added[0]))
  })

  it('keep the marker in every copy, of every kind', () => {
    const makers: Array<[string, () => object]> = [
      ['object', () => ({ a: 1 })],
      ['array', () => [1, 2]],
      ['Map', () => new Map([[1, 2]])],
      ['Set', () => new Set([1])],
      ['Date', () => new Date(1)],
      ['ArrayBuffer', () => new ArrayBuffer(2)],
      ['Uint8Array', () => new Uint8Array([1, 2])],
      ['DataView', () => new DataView(new ArrayBuffer(2))],
      ['URL', () => new URL('https://a.test/?x=1')],
      ['URLSearchParams', () => new URLSearchParams('x=1')],
    ]
    for (const [name, make] of makers) {
      assert.isTrue(
        marked((snapshot({ v: markRaw(make()) }) as { v: object }).v),
        `snapshot ${name}`,
      )
      const current: { v: object } = { v: Object.freeze({}) }
      reconcile(current, { v: markRaw(make()) })
      assert.isTrue(marked(current.v), `reconcile ${name}`)
      // Each kind changed through its draft, so the result holds a copy.
      const changed = produce({ v: markRaw(make()) }, (draft) => {
        const value = draft.v as object & Record<string, unknown>
        if (value instanceof Map) value.set(3, 4)
        else if (value instanceof Set) value.add(3)
        else if (value instanceof Date) value.setTime(5)
        else if (value instanceof ArrayBuffer) new Uint8Array(value)[0] = 9
        else if (value instanceof DataView) value.setUint8(0, 9)
        else if (value instanceof URL) value.hash = 'h'
        else if (value instanceof URLSearchParams) value.set('x', '2')
        else value[0] = 9
        return draft
      })
      assert.isTrue(marked(changed.v), `produce ${name}`)
    }
  })

  it('keep the marker on a copy reconcile adds to reactive state, which stays raw', () => {
    const list: object = { a: 1 }
    const state = reactive({ list })
    reconcile(state, { list: markRaw([1, 2]) })
    assert.isFalse(isReactive(state.list))
  })

  it('are serialized without the marker', () => {
    const value = { a: markRaw({ x: 1 }), b: markRaw([1]) }
    const copy = deserialize(serialize(value), { maxBytes: 1024 }) as { a: object; b: unknown }
    assert.deepEqual(copy, { a: { x: 1 }, b: [1] })
    assert.isFalse(Object.hasOwn(copy.a, '__v_skip'))
  })

  it('lose an enumerable __v_skip that next lacks, as any other data', () => {
    const current: Record<string, unknown> = { __v_skip: true, n: 1 }
    reconcile(current, { n: 2 })
    assert.deepEqual(current, { n: 2 })
  })
})

describe('objects reconcile adds to reactive state', () => {
  // Vue stores a deep reactive value as its raw object, so raw state holds no proxies.
  const proxies = (value: unknown, seen = new Set<object>()): number => {
    if (typeof value !== 'object' || value === null || seen.has(value)) return 0
    seen.add(value)
    let count = toRaw(value) === value ? 0 : 1
    const raw = toRaw(value)
    const children =
      raw instanceof Map
        ? [...raw.keys(), ...raw.values()]
        : raw instanceof Set
          ? [...raw]
          : Object.values(raw)
    for (const child of children) count += proxies(child, seen)
    return count
  }

  it('hold raw objects, as Vue stores them, nested, shared and cyclic', () => {
    const shared = { s: 1 }
    const cycle: Record<string, unknown> = { c: 1 }
    cycle.self = cycle
    const key = { k: 1 }
    const state = reactive<Record<string, unknown>>({ root: 1 })
    reconcile(state, {
      root: {
        cycle,
        list: [{ x: { y: {} } }, shared],
        map: new Map([[key, { key }]]),
        nested: { a: { b: {} } },
        set: new Set([{ z: 1 }, shared]),
        shared,
      },
    })
    const raw = toRaw(state)
    assert.equal(proxies(raw.root), 0)
    const root = raw.root as { cycle: { self: unknown }; list: unknown[]; shared: unknown }
    assert.equal(root.cycle.self, root.cycle)
    assert.equal(root.list[1], root.shared)
    assert.doesNotThrow(() => structuredClone(raw))
    const view = state.root as { cycle: { self: unknown }; list: unknown[]; shared: unknown }
    assert.isTrue(isReactive(view.cycle))
    assert.equal(view.cycle.self, view.cycle)
    assert.equal(view.list[1], view.shared)
  })

  it('keep a proxy at an own __proto__ key, which Vue reads without wrapping', () => {
    const cycle: Record<string, unknown> = {}
    Object.defineProperty(cycle, '__proto__', {
      configurable: true,
      enumerable: true,
      value: cycle,
      writable: true,
    })
    const state = reactive<Record<string, unknown>>({ root: 1 })
    reconcile(state, { root: cycle })
    const view = state.root as Record<string, unknown>
    assert.isTrue(isReactive(view))
    assert.equal(Object.getOwnPropertyDescriptor(toRaw(view), '__proto__')?.value, view)
  })
})

/** Whether `value` holds Vue's `markRaw` marker. */
const marked = (value: object): boolean =>
  Object.getOwnPropertyDescriptor(value, '__v_skip')?.enumerable === false

/** A raw object and its Vue reactive proxy. */
function pair(): { raw: { n: number }; wrapped: { n: number } } {
  const raw = { n: 0 }
  return { raw, wrapped: reactive(raw) }
}

describe('a Vue proxy and its raw object', () => {
  it('have one draft', () => {
    const { raw, wrapped } = pair()
    const current = { p: wrapped, r: raw }
    let same = false
    const result = produce(current, (draft) => {
      same = draft.p === draft.r
      return draft
    })
    assert.isTrue(same)
    assert.equal(result, current)
  })

  it('become one new object wherever either is when the recipe changes it', () => {
    const { raw, wrapped } = pair()
    const current = { deep: { p: wrapped }, p: wrapped, r: raw }
    // The recipe reaches the object only through its raw form.
    const result = produce(current, (draft) => {
      draft.r.n = 1
      return draft
    })
    assert.equal(raw.n, 0)
    assert.equal(result.r.n, 1)
    assert.equal(result.p, result.r)
    assert.equal(result.deep.p, result.r)
    assert.isFalse(isReactive(result.r))
  })

  it('stay each where it was when the recipe changes something else', () => {
    const { raw, wrapped } = pair()
    const current = { flag: 0, list: [wrapped, raw, wrapped], p: wrapped, r: raw }
    const result = produce(current, (draft) => {
      draft.flag = 1
      draft.list.push(wrapped)
      return draft
    })
    assert.notEqual(result, current)
    assert.equal(result.p, wrapped)
    assert.equal(result.r, raw)
    assert.deepEqual(
      result.list.map((item) => (item === raw ? 'raw' : item === wrapped ? 'proxy' : 'other')),
      ['proxy', 'raw', 'proxy', 'proxy'],
    )
    assert.equal(
      produce(current, (draft) => draft.r),
      raw,
    )
    assert.equal(
      produce(current, (draft) => draft.p),
      wrapped,
    )
  })

  it('are one copy in snapshot, also through the seen map', () => {
    const { raw, wrapped } = pair()
    const copy = snapshot({ p: wrapped, r: raw }) as { p: object; r: object }
    assert.equal(copy.p, copy.r)
    const seen = new WeakMap<object, object>()
    const first = snapshot(wrapped, seen)
    assert.equal(snapshot(raw, seen), first)
    assert.equal(seen.get(raw), first)
    const reversed = new WeakMap<object, object>()
    const raws = snapshot(raw, reversed)
    assert.equal(snapshot(readonly(raw), reversed), raws)
  })

  it('updated through reconcile hold one object where next holds one', () => {
    const { raw, wrapped } = pair()
    const current = { p: wrapped, r: raw }
    reconcile(
      current,
      produce(current, (draft) => {
        draft.p.n = 2
        return draft
      }),
    )
    assert.equal(raw.n, 2)
    assert.equal(toRaw(current.r), raw)
    assert.equal(current.p, current.r)
  })

  it('cannot be two keys or members of an ordinary Map or Set', () => {
    const { raw, wrapped } = pair()
    for (const collection of [
      new Map<object, number>([
        [raw, 1],
        [wrapped, 2],
      ]),
      // Both orders: the second view is found through the first.
      new Map<object, number>([
        [wrapped, 1],
        // eslint-disable-next-line perfectionist/sort-maps
        [raw, 2],
      ]),
      new Set<object>([raw, wrapped]),
      // eslint-disable-next-line perfectionist/sort-sets
      new Set<object>([wrapped, raw]),
    ]) {
      assert.equal(
        errorType(() => snapshot(collection)),
        'SnapshotWrapperKeyDuplicated',
      )
      assert.equal(
        errorType(() => serialize(collection)),
        'SerializeValueUnsupported',
      )
      assert.equal(
        errorType(() =>
          reconcile({ c: collection instanceof Map ? new Map() : new Set() }, { c: collection }),
        ),
        'PublicationRejected',
      )
      const current = { c: collection, r: raw }
      assert.equal(
        produce(current, (draft) => draft.c),
        collection,
      )
      assert.equal(
        errorType(() =>
          produce(current, (draft) => {
            draft.r.n = 1
            return draft
          }),
        ),
        'FinalizationConstructionImpossible',
      )
    }
    // Whichever view is met first, also outside the collection.
    for (const before of [raw, wrapped, readonly(raw)])
      for (const members of [
        [raw, wrapped],
        [wrapped, raw],
        [readonly(raw), wrapped],
      ]) {
        const value = { before, set: new Set<object>(members) }
        assert.equal(
          errorType(() => serialize(value)),
          'SerializeValueUnsupported',
        )
        assert.equal(
          errorType(() => snapshot(value)),
          'SnapshotWrapperKeyDuplicated',
        )
      }
    // Held once, each is an ordinary key or member.
    assert.equal((snapshot(new Map([[raw, 1]])) as Map<object, number>).size, 1)
    assert.equal(
      (
        deserialize(serialize({ m: new Set([raw]), p: wrapped }), { maxBytes: Infinity }) as {
          m: Set<unknown>
        }
      ).m.size,
      1,
    )
    assert.equal(raw.n, 0)
  })
})

describe('a draft of a Vue proxy and its raw object', () => {
  it('finds a Map key or Set member through either', () => {
    const raw = { id: 1 }
    const wrapped = reactive(raw)
    const set = produce({ p: wrapped, s: new Set<object>([raw]) }, (draft) => {
      assert.isTrue(draft.s.has(draft.p))
      for (const member of draft.s) draft.s.delete(member)
      return draft
    }).s
    assert.equal(set.size, 0)
    const map = produce(
      { m: new Map<object, string>([[raw, 'v']]), p: wrapped, r: raw },
      (draft) => {
        assert.equal(draft.p, draft.r)
        draft.m.set(draft.r, 'w')
        return draft
      },
    ).m
    assert.deepEqual([...map], [[raw, 'w']])
    // In plain state a search for a raw object does not look for a proxy of it.
    const plain = produce({ m: new Map<object, string>([[wrapped, 'v']]), r: raw }, (draft) => {
      draft.m.set(draft.r, 'w')
      return draft
    }).m
    assert.deepEqual(
      [...plain],
      [
        [wrapped, 'v'],
        [raw, 'w'],
      ],
    )
    const byProxy = produce(
      reactive({ m: new Map<object, string>([[wrapped, 'v']]), r: raw }),
      (draft) => {
        draft.m.set(draft.r, 'w')
        return draft
      },
    ).m
    assert.deepEqual(
      [...byProxy].map(([key, value]) => [toRaw(key), value]),
      [[raw, 'w']],
    )
    // A search for a Vue proxy finds its raw object in plain state.
    produce({ list: [raw], m: new Map<object, number>([[raw, 1]]) }, (draft) => {
      assert.isTrue(draft.list.includes(reactive(raw)))
      assert.equal(draft.m.get(reactive(raw)), 1)
      return draft
    })
  })

  it('updates the key a reactive Map holds through either', () => {
    const key = {}
    const rawMap = new Map<object, number>([[key, 1]])
    const result = produce({ pm: reactive(rawMap), rm: rawMap }, (draft) => {
      assert.equal(draft.rm.size, 1)
      draft.pm.set(reactive(key), 2)
      return draft
    })
    assert.deepEqual([...result.rm], [[key, 2]])
    assert.equal(result.pm, result.rm)
  })

  it('leaves a SharedArrayBuffer and its mark as they are', () => {
    const shared = markRaw(new SharedArrayBuffer(4))
    const before = Object.getOwnPropertyDescriptor(shared, '__v_skip')
    const current = { v: new Uint8Array(shared) }
    assert.equal(
      produce(current, (draft) => {
        assert.equal(draft.v[0], 0)
        return draft
      }),
      current,
    )
    assert.deepEqual(Object.getOwnPropertyDescriptor(shared, '__v_skip'), before)
    assert.isTrue(Object.isExtensible(shared))
  })

  it('keep a frozen marked copy frozen', () => {
    const map = Object.freeze(markRaw(new Map([['a', { n: 1 }]])))
    const result = produce({ map }, (draft) => {
      draft.map.get('a')!.n = 2
      return draft
    })
    assert.isTrue(Object.isFrozen(result.map))
    assert.isTrue(marked(result.map))
  })
})

describe('reconcile and snapshot with a Vue proxy kept or remembered', () => {
  it('reject a Map or Set of both views when one is kept in place', () => {
    const { raw, wrapped } = pair()
    assert.equal(
      errorType(() => reconcile({ b: raw, s: new Set() }, { b: raw, s: new Set([raw, wrapped]) })),
      'PublicationRejected',
    )
    assert.equal(
      errorType(() =>
        // eslint-disable-next-line perfectionist/sort-sets
        reconcile({ b: wrapped, s: new Set() }, { b: wrapped, s: new Set([wrapped, raw]) }),
      ),
      'PublicationRejected',
    )
    // The raw object elsewhere is the kept proxy.
    const current: Record<string, object> = { b: wrapped }
    reconcile(current, { a: raw, b: wrapped })
    assert.equal(current.a, current.b)
  })

  it('reject both views as keys through the seen map, and only them', () => {
    const { raw, wrapped } = pair()
    const seen = new WeakMap<object, object>()
    snapshot(wrapped, seen)
    assert.equal(
      // eslint-disable-next-line perfectionist/sort-sets
      errorType(() => snapshot(new Set([wrapped, raw]), seen)),
      'SnapshotWrapperKeyDuplicated',
    )
    const first = {}
    const second = {}
    const copy = snapshot(
      {
        m: new Map([
          [first, 1],
          [second, 2],
        ]),
        x: reactive({}),
      },
      new WeakMap([
        [first, {}],
        [second, {}],
      ]),
    ) as { m: Map<object, number> }
    assert.equal(copy.m.size, 2)
  })
})
