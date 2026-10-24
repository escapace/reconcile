import { assert, it } from 'vitest'
import { effect, isReactive, reactive, readonly, shallowReactive, toRaw } from 'vue'

import { snapshot } from '../index'
import { decodeText, encodeText } from './fixtures/text-codec'

it('encodes Vue wrappers as the data they expose', () => {
  const data = { list: [1, 2], user: { name: 'Ada' } }
  for (const wrapped of [reactive(data), readonly(data), shallowReactive(data)])
    assert.equal(encodeText(wrapped), encodeText(data))
  const map = new Map([['k', { v: 1 }]])
  const set = new Set([1, 2])
  assert.equal(encodeText(reactive(map)), encodeText(map))
  assert.equal(encodeText(reactive(set)), encodeText(set))
})

it('restores plain data, and restores a wrapper and its raw object as one object', () => {
  const raw = { x: 1 }
  const copy = decodeText(encodeText({ raw, wrapped: reactive(raw) })) as Record<string, object>
  assert.isFalse(isReactive(copy))
  assert.isFalse(isReactive(copy.wrapped))
  assert.equal(copy.raw, copy.wrapped)
  assert.deepEqual(copy.raw, { x: 1 })
  const reversed = decodeText(encodeText([readonly(raw), raw, reactive(raw)])) as object[]
  assert.equal(reversed[0], reversed[1])
  assert.equal(reversed[1], reversed[2])
})

it('reads through the wrappers, so an enclosing effect tracks what it encoded', () => {
  const store = reactive({ user: { name: 'Ada' } })
  let runs = 0
  effect(() => {
    runs++
    encodeText(store)
  })
  store.user.name = 'Grace'
  assert.equal(runs, 2)
  toRaw(store).user.name = 'Raw'
  assert.equal(runs, 2)
})

it('copies the same data from toRaw without tracking it', () => {
  const store = reactive({
    list: [{ a: 1 }],
    map: new Map([['k', { v: 1 }]]),
    user: { name: 'Ada' },
  })
  store.list.push({ a: 2 })
  assert.deepEqual(snapshot(toRaw(store)), snapshot(store))
  let runs = 0
  effect(() => {
    runs++
    snapshot(toRaw(store))
  })
  store.user.name = 'Grace'
  store.map.get('k')!.v = 2
  assert.equal(runs, 1)
})
