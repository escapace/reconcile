import { assert, it } from 'vitest'
import { reactive, watch } from 'vue'
import { reconcile } from '../index'

// A Map that counts its writes; reconcile writes through the object's own methods.
class Logged extends Map<string, number> {
  writes = 0

  override delete(key: string): boolean {
    this.writes += 1
    return super.delete(key)
  }

  override set(key: string, value: number): this {
    this.writes += 1
    return super.set(key, value)
  }
}

function random(seed: number): () => number {
  let state = seed
  return () => {
    state = (Math.imul(state, 1_103_515_245) + 12_345) >>> 0
    return state / 4_294_967_296
  }
}

it('reaches the next entries writing only changed values and the entries from the first new key', () => {
  for (let seed = 1; seed <= 400; seed += 1) {
    const next = random(seed)
    const entries = (): Array<[string, number]> => {
      const keys = ['a', 'b', 'c', 'd', 'e'].filter(() => next() < 0.7)
      if (next() < 0.5) keys.reverse()
      return keys.map((key) => [key, Math.floor(next() * 3)])
    }
    const before = entries()
    const after = entries()
    const map = new Logged(before)
    map.writes = 0
    reconcile({ map }, { map: new Map(after) })
    assert.deepEqual([...map], after, `seed ${seed}`)
    let position = 0
    while (
      position < before.length &&
      position < after.length &&
      before[position][0] === after[position][0]
    )
      position += 1
    let expected = before.length - position + (after.length - position)
    for (let index = 0; index < position; index += 1)
      if (before[index][1] !== after[index][1]) expected += 1
    assert.equal(map.writes, expected, `seed ${seed}`)
  }
})

it('triggers no dependent of an unchanged Map entry or Set member', () => {
  const state = reactive({
    counts: new Map([
      ['a', 1],
      ['b', 2],
    ]),
    tags: new Set(['x', 'y']),
  })
  let entry = 0
  let member = 0
  watch(
    () => state.counts.get('a'),
    () => (entry += 1),
    { flush: 'sync' },
  )
  watch(
    () => state.tags.has('x'),
    () => (member += 1),
    { flush: 'sync' },
  )
  reconcile(state, {
    counts: new Map([
      ['a', 1],
      ['b', 3],
    ]),
    tags: new Set(['x', 'z']),
  })
  assert.equal(entry, 0)
  assert.equal(member, 0)
  assert.deepEqual(
    [...state.counts],
    [
      ['a', 1],
      ['b', 3],
    ],
  )
  assert.deepEqual([...state.tags], ['x', 'z'])
})
