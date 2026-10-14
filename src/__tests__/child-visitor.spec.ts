import { describe, expect, it } from 'vitest'
import { arrayType } from '../types/array'
import { mapType } from '../types/map'
import { setType } from '../types/set'

describe('native child visitor', () => {
  it('visits map keys before values and stops without reading later entries', () => {
    const seen: unknown[] = []
    const source = new Map([
      [1, 2],
      [3, 4],
    ])
    expect(
      mapType.policy.someChild(source, Reflect.get, (value) => {
        seen.push(value)
        return value === 3
      }),
    ).toBe(true)
    expect(seen).toEqual([1, 2, 3])
  })

  for (const kind of ['map', 'set'] as const) {
    for (const outcome of ['match', 'throw', 'exhaust'] as const) {
      it(`${kind} closes its iterator on ${outcome}`, () => {
        let closed = 0
        const failure = new Error('predicate')
        const seen: unknown[] = []
        const source = kind === 'map' ? new Map() : new Set()
        Object.defineProperty(source, Symbol.iterator, {
          *value() {
            try {
              yield kind === 'map' ? [1, 2] : 1
              yield kind === 'map' ? [3, 4] : 3
            } finally {
              closed += 1
            }
          },
        })
        const visit = () =>
          (kind === 'map' ? mapType : setType).policy.someChild(source, Reflect.get, (value) => {
            seen.push(value)
            if (outcome === 'throw') throw failure
            return outcome === 'match'
          })
        let result: unknown
        try {
          result = visit()
        } catch (error) {
          result = error
        }
        expect(result).toBe(outcome === 'throw' ? failure : outcome === 'match')
        expect(closed).toBe(1)
        expect(seen).toEqual(outcome === 'exhaust' ? (kind === 'map' ? [1, 2, 3, 4] : [1, 3]) : [1])
      })
    }
  }

  it('skips array holes and rechecks length after each child', () => {
    const source = [1, 2, 3]
    Reflect.deleteProperty(source, 1)
    const seen: unknown[] = []
    expect(
      arrayType.policy.someChild(source, Reflect.get, (value) => {
        seen.push(value)
        if (value === 1) source.push(4)
        return false
      }),
    ).toBe(false)
    expect(seen).toEqual([1, 3, 4])
  })
})
