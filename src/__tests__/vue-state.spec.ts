import { assert, describe, it, vi } from 'vitest'
import { isReactive, isRef, markRaw, reactive, readonly, ref, shallowRef, toRaw, watch } from 'vue'

import { isReconcileError, produce, reconcile } from '../index'
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

  it('lose an enumerable __v_skip that next lacks, as any other data', () => {
    const current: Record<string, unknown> = { __v_skip: true, n: 1 }
    reconcile(current, { n: 2 })
    assert.deepEqual(current, { n: 2 })
  })
})
