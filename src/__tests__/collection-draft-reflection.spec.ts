import { assert, it } from 'vitest'
import { produce } from '../index'

class Registry extends Map<string, number> {}

const sources = (): { map: Map<unknown, unknown> } & Record<
  string,
  Map<unknown, unknown> | Set<unknown>
> => ({
  map: new Map([['k', { n: 1 }]]),
  registry: new Registry([['k', 1]]),
  set: new Set([1]),
})

it('gives a Map or Set draft the own keys of its source', () => {
  const current = sources()
  produce(current, (draft) => {
    for (const name of Object.keys(current)) {
      const collection = draft[name]
      assert.deepEqual(Reflect.ownKeys(collection), Reflect.ownKeys(current[name]), name)
      assert.deepEqual(Reflect.ownKeys({ ...collection }), [], name)
    }
    return draft
  })
})

it('copies nothing of a Map or Set draft into a spread or Object.assign', () => {
  const current = sources()
  const result = produce(current, (draft) => {
    const copies: Record<string, unknown> = {}
    for (const name of Object.keys(current)) {
      copies[`${name}Spread`] = { ...draft[name] }
      copies[`${name}Assigned`] = Object.assign({}, draft[name])
    }
    return { ...draft, copies }
  })
  for (const [name, copy] of Object.entries(result.copies)) {
    assert.deepEqual(Reflect.ownKeys(copy as object), [], name)
  }
  assert.strictEqual(result.map, current.map)
})
