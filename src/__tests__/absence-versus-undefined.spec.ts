import { assert, describe, it } from 'vitest'

import { createPatch, patch, reconcile } from '../index'

describe('absence versus undefined semantics', () => {
  describe('plain objects', () => {
    it('reconcile distinguishes omitted properties from present undefined properties', () => {
      const current: {
        keep: number
        remove?: number
        value?: number | undefined
      } = {
        keep: 1,
        remove: 2,
      }
      const next: {
        keep: number
        remove?: number
        value?: number | undefined
      } = {
        keep: 1,
        value: undefined,
      }

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal('remove' in result, false)
      assert.equal('value' in result, true)
      assert.equal(result.value, undefined)
      assert.deepEqual(Reflect.ownKeys(result), ['keep', 'value'])
    })

    it('reconcile treats a property named "undefined" as an ordinary property key', () => {
      const weirdKey = String(undefined)
      const current: Record<string, number | undefined> = {
        keep: 1,
        remove: 2,
      }
      const next: Record<string, number | undefined> = {
        keep: 1,
        value: undefined,
      }
      next[weirdKey] = 3

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal('remove' in result, false)
      assert.equal('value' in result, true)
      assert.equal(result.value, undefined)
      assert.equal(weirdKey in result, true)
      assert.equal(result[weirdKey], 3)
      assert.deepEqual(Reflect.ownKeys(result), ['keep', 'value', 'undefined'])
    })

    it('patch publishes the same distinction for object properties', () => {
      const current: {
        keep: true
        remove?: number
        value?: number | undefined
      } = {
        keep: true,
        remove: 1,
      }

      const result = patch(current, (draft) => {
        delete draft.remove
        draft.value = undefined
        return draft
      })

      assert.equal(result, current)
      assert.equal('remove' in result, false)
      assert.equal('value' in result, true)
      assert.equal(result.value, undefined)
      assert.deepEqual(Reflect.ownKeys(result), ['keep', 'value'])
    })
  })

  describe('arrays', () => {
    it('reconcile preserves a hole when the next array has a hole', () => {
      const current = [1, 2, 3] as Array<number | undefined>
      // eslint-disable-next-line no-sparse-arrays
      const next = [1, , 3] as Array<number | undefined>

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal(result.length, 3)
      assert.equal(1 in result, false)
      assert.equal(result[1], undefined)
    })

    it('reconcile materializes a present undefined element when the next array has one', () => {
      // eslint-disable-next-line no-sparse-arrays
      const current = [1, , 3] as Array<number | undefined>
      const next = [1, undefined, 3] as Array<number | undefined>

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal(result.length, 3)
      assert.equal(1 in result, true)
      assert.equal(result[1], undefined)
      assert.deepEqual(Object.keys(result), ['0', '1', '2'])
    })

    it('reconcile materializes a trailing undefined element when the next array grows', () => {
      const current = [1, 2] as Array<number | undefined>
      const next = [1, 2, undefined] as Array<number | undefined>

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal(result.length, 3)
      assert.equal(2 in result, true)
      assert.equal(result[2], undefined)
      assert.deepEqual(Object.keys(result), ['0', '1', '2'])
    })

    it('reconcile materializes multiple trailing undefined elements when the next array grows', () => {
      const current = [1] as Array<number | undefined>
      const next = [1, undefined, undefined] as Array<number | undefined>

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal(result.length, 3)
      assert.equal(1 in result, true)
      assert.equal(2 in result, true)
      assert.equal(result[1], undefined)
      assert.equal(result[2], undefined)
      assert.deepEqual(Object.keys(result), ['0', '1', '2'])
    })

    it('reconcile materializes only the explicit undefined slots when growth mixes values and undefined', () => {
      const current = [1] as Array<number | undefined>
      const next = [1, undefined, 3, undefined] as Array<number | undefined>

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal(result.length, 4)
      assert.equal(1 in result, true)
      assert.equal(2 in result, true)
      assert.equal(3 in result, true)
      assert.equal(result[1], undefined)
      assert.equal(result[2], 3)
      assert.equal(result[3], undefined)
      assert.deepEqual(Object.keys(result), ['0', '1', '2', '3'])
    })

    it('reconcile materializes a retained undefined slot even when the array shrinks', () => {
      // eslint-disable-next-line no-sparse-arrays
      const current = [1, , 3] as Array<number | undefined>
      const next = [1, undefined] as Array<number | undefined>

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal(result.length, 2)
      assert.equal(1 in result, true)
      assert.equal(result[1], undefined)
      assert.deepEqual(Object.keys(result), ['0', '1'])
    })

    it('createPatch preserves the difference between a hole and a present undefined element', () => {
      const current = [1, 2] as Array<number | undefined>

      const result = createPatch(current, (draft) => {
        draft.length = 4
        Reflect.deleteProperty(draft, 1)
        draft[2] = undefined
        draft[3] = 4
        return draft
      })

      assert.equal(result.length, 4)
      assert.equal(1 in result, false)
      assert.equal(2 in result, true)
      assert.equal(result[2], undefined)
      assert.equal(3 in result, true)
      assert.equal(result[3], 4)
      assert.deepEqual(Object.keys(result), ['0', '2', '3'])
    })

    it('patch publishes a trailing undefined element as present, not as a hole', () => {
      const current = {
        list: [1, 2] as Array<number | undefined>,
      }

      const result = patch(current, (draft) => {
        draft.list[2] = undefined
        return draft
      })

      assert.equal(result, current)
      assert.equal(result.list.length, 3)
      assert.equal(2 in result.list, true)
      assert.equal(result.list[2], undefined)
      assert.deepEqual(Object.keys(result.list), ['0', '1', '2'])
    })

    it('patch publishes push(undefined) as a present trailing element', () => {
      const current = [1, 2] as Array<number | undefined>

      const result = patch(current, (draft) => {
        draft.push(undefined)
        return draft
      })

      assert.equal(result, current)
      assert.equal(result.length, 3)
      assert.equal(2 in result, true)
      assert.equal(result[2], undefined)
      assert.deepEqual(Object.keys(result), ['0', '1', '2'])
    })

    it('patch publishes splice insertion of undefined as present elements', () => {
      const current = [1, 4] as Array<number | undefined>

      const result = patch(current, (draft) => {
        draft.splice(1, 0, undefined, 3)
        return draft
      })

      assert.equal(result, current)
      assert.equal(result.length, 4)
      assert.equal(1 in result, true)
      assert.equal(2 in result, true)
      assert.equal(result[1], undefined)
      assert.equal(result[2], 3)
      assert.equal(result[3], 4)
      assert.deepEqual(Object.keys(result), ['0', '1', '2', '3'])
    })
  })

  describe('maps', () => {
    it('reconcile distinguishes an absent entry from a present undefined value', () => {
      const current = new Map<string, number | undefined>([
        ['keep', 1],
        ['remove', 2],
      ])
      const next = new Map<string, number | undefined>([
        ['added', undefined],
        ['keep', undefined],
      ])

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal(result.has('remove'), false)
      assert.equal(result.has('keep'), true)
      assert.equal(result.get('keep'), undefined)
      assert.equal(result.has('added'), true)
      assert.equal(result.get('added'), undefined)
      assert.deepEqual(Array.from(result.keys()), ['added', 'keep'])
    })

    it('reconcile treats undefined as an ordinary map key distinct from the string "undefined"', () => {
      const current = new Map<string | undefined, number | undefined>([
        ['remove', 1],
        ['undefined', 2],
      ])
      const next = new Map<string | undefined, number | undefined>([
        ['undefined', 3],
        [undefined, undefined],
      ])

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal(result.has('remove'), false)
      assert.equal(result.has(undefined), true)
      assert.equal(result.get(undefined), undefined)
      assert.equal(result.has('undefined'), true)
      assert.equal(result.get('undefined'), 3)
      assert.deepEqual(Array.from(result.keys()), ['undefined', undefined])
    })

    it('patch preserves present undefined map values and undefined map keys', () => {
      const current = {
        map: new Map<string | undefined, number | undefined>([['remove', 1]]),
      }

      const result = patch(current, (draft) => {
        draft.map.delete('remove')
        draft.map.set(undefined, undefined)
        draft.map.set('undefined', undefined)
        return draft
      })

      assert.equal(result, current)
      assert.equal(result.map.has('remove'), false)
      assert.equal(result.map.has(undefined), true)
      assert.equal(result.map.get(undefined), undefined)
      assert.equal(result.map.has('undefined'), true)
      assert.equal(result.map.get('undefined'), undefined)
      assert.deepEqual(Array.from(result.map.keys()), [undefined, 'undefined'])
    })
  })

  describe('sets', () => {
    it('reconcile distinguishes absent membership from present undefined membership', () => {
      const current = new Set<number | undefined>([1, 2])
      const next = new Set<number | undefined>([2, undefined])

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal(result.has(1), false)
      assert.equal(result.has(2), true)
      assert.equal(result.has(undefined), true)
      assert.deepEqual(Array.from(result.values()), [2, undefined])
    })

    it('reconcile treats undefined as an ordinary set value distinct from the string "undefined"', () => {
      const current = new Set<string | undefined>(['remove'])
      const next = new Set<string | undefined>([undefined, 'undefined'])

      const result = reconcile(current, next)

      assert.equal(result, current)
      assert.equal(result.has('remove'), false)
      assert.equal(result.has(undefined), true)
      assert.equal(result.has('undefined'), true)
      assert.deepEqual(Array.from(result.values()), [undefined, 'undefined'])
    })

    it('patch preserves present undefined membership', () => {
      const current = {
        set: new Set<number | undefined>([1]),
      }

      const result = patch(current, (draft) => {
        draft.set.delete(1)
        draft.set.add(undefined)
        return draft
      })

      assert.equal(result, current)
      assert.equal(result.set.has(1), false)
      assert.equal(result.set.has(undefined), true)
      assert.deepEqual(Array.from(result.set.values()), [undefined])
    })
  })
})
