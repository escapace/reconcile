import { describe, expect, it } from 'vitest'
import { arrayImmutable } from '../types/array'
import { mapImmutable } from '../types/map'
import { setImmutable } from '../types/set'

describe('native child visitor', () => {
  it('visits map keys before values and stops without reading later entries', () => {
    const seen: unknown[] = []
    const source = new Map([
      [1, 2],
      [3, 4],
    ])
    expect(
      mapImmutable.someChild(source, Reflect.get, (value) => {
        seen.push(value)
        return value === 3
      }),
    ).toBe(true)
    expect(seen).toEqual([1, 2, 3])
  })

  // An override of the iterator, on the instance or a subclass, is never called: the walk reads
  // the built-in contents, stops at a match and lets an exception through.
  for (const kind of ['map', 'set'] as const) {
    for (const outcome of ['match', 'throw', 'exhaust'] as const) {
      it(`${kind} walks its built-in contents on ${outcome}`, () => {
        let overridden = 0
        const failure = new Error('predicate')
        const seen: unknown[] = []
        const source =
          kind === 'map'
            ? new Map([
                [1, 2],
                [3, 4],
              ])
            : new Set([1, 3])
        Object.defineProperty(source, Symbol.iterator, {
          *value() {
            overridden += 1
            yield* []
          },
        })
        const visit = () =>
          (kind === 'map' ? mapImmutable : setImmutable).someChild(source, Reflect.get, (value) => {
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
        expect(overridden).toBe(0)
        expect(seen).toEqual(outcome === 'exhaust' ? (kind === 'map' ? [1, 2, 3, 4] : [1, 3]) : [1])
      })
    }
  }

  it('skips array holes and rechecks length after each child', () => {
    const source = [1, 2, 3]
    Reflect.deleteProperty(source, 1)
    const seen: unknown[] = []
    expect(
      arrayImmutable.someChild(source, Reflect.get, (value) => {
        seen.push(value)
        if (value === 1) source.push(4)
        return false
      }),
    ).toBe(false)
    expect(seen).toEqual([1, 3, 4])
  })
})
