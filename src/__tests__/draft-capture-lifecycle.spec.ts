import { assert, it } from 'vitest'

import { produce } from '../index'

it('registers mixed container cycles before capturing their ordered accessor edges', () => {
  const observations: string[] = []
  const current = {
    array: [] as object[],
    flag: 0,
    map: new Map<object, object>(),
    object: {},
    set: new Set<object>(),
  }
  const node = (label: string) => ({
    parent: current,
    get observed(): object {
      observations.push(label)
      return this.parent
    },
  })
  const arrayChild = node('array-child')
  const mapKey = node('map-key')
  const mapValue = node('map-value')
  const objectChild = node('object-child')
  const setChild = node('set-child')
  Object.defineProperty(current.array, '0', {
    configurable: true,
    enumerable: true,
    get: () => {
      observations.push('array-slot')
      return arrayChild
    },
  })
  current.map.set(mapKey, mapValue)
  current.object = objectChild
  current.set.add(setChild)

  const next = produce(current, (draft) => {
    draft.flag = 1
    return draft
  })

  assert.deepEqual(observations, [
    'array-slot',
    'array-child',
    'map-key',
    'map-value',
    'object-child',
    'set-child',
  ])
  assert.equal(current.flag, 0)
  assert.equal(next.flag, 1)
  assert.notEqual(next.array, current.array)
  assert.notEqual(next.map, current.map)
  assert.notEqual(next.object, current.object)
  assert.notEqual(next.set, current.set)
  assert.equal(next.map.size, 1)
  assert.equal(next.set.size, 1)
  assert.equal(next.array.length, 1)
  const [nextKey, nextValue] = [...next.map][0]
  const nextMember = [...next.set][0]
  for (const [original, finalized] of [
    [arrayChild, next.array[0]],
    [mapKey, nextKey],
    [mapValue, nextValue],
    [objectChild, next.object],
    [setChild, nextMember],
  ] as const) {
    assert.notEqual(finalized, original)
    assert.equal(original.parent, current)
    assert.equal(Reflect.get(finalized, 'parent'), next)
    assert.deepEqual(Object.getOwnPropertyDescriptor(finalized, 'observed'), {
      configurable: true,
      enumerable: true,
      value: next,
      writable: true,
    })
  }
})
