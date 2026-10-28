import { assert, describe, it } from 'vitest'
import { produce } from '../produce'
import { reconcile } from '../reconcile'
import { ReconcileError, snapshot } from '../index'
import { bytesOf, firstMapEntry, firstSetEntry } from './fixtures/contents'
import { assertWouldChangeNext } from './fixtures/graph-state'

class UnsupportedCounter {
  value: number

  constructor(value: number) {
    this.value = value
  }
}

const returnedValue = () => 'ok'

interface PublicationCyclic {
  nested: { count: number }
  self?: PublicationCyclic
}

describe('caller publication', () => {
  it('mutates a draft and publishes through reconcile while retaining compatible identities', () => {
    const current = {
      keep: { ok: true },
      list: [{ id: 1 }],
      nested: { count: 0 },
    }
    const keepReference = current.keep
    const listReference = current.list
    const nestedReference = current.nested

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.list.push({ id: 2 })
        draft.nested.count = 1
        return draft
      }),
    )

    assert.equal(result, current)
    assert.equal(result.keep, keepReference)
    assert.equal(result.list, listReference)
    assert.equal(result.nested, nestedReference)
    assert.deepEqual(result, {
      keep: { ok: true },
      list: [{ id: 1 }, { id: 2 }],
      nested: { count: 1 },
    })
  })

  it('does not leak draft-side mutations to the live current graph before publication', () => {
    const current = {
      nested: { count: 0 },
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.nested.count = 1
        assert.equal(current.nested.count, 0)
        return draft
      }),
    )

    assert.equal(result, current)
    assert.equal(current.nested.count, 1)
  })

  it('keeps a read-only recipe on the exact current graph when nothing changed', () => {
    const current = {
      nested: { count: 0 },
    }
    const nestedReference = current.nested

    const result = reconcile(
      current,
      produce(current, (draft) => {
        assert.equal(draft.nested.count, 0)
        return draft
      }),
    )

    assert.equal(result, current)
    assert.equal(result.nested, nestedReference)
  })

  it('reuses the exact current graph after reverted object mutations', () => {
    const current = {
      nested: { count: 0 },
    }
    const nestedReference = current.nested

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.nested.count = 1
        draft.nested.count = 0
        return draft
      }),
    )

    assert.equal(result, current)
    assert.equal(result.nested, nestedReference)
    assert.deepEqual(result, { nested: { count: 0 } })
  })

  it('reuses the original special value when it was only read, not changed', () => {
    const current = {
      date: new Date('2024-01-01T00:00:00.000Z'),
    }
    const dateReference = current.date

    const result = reconcile(
      current,
      produce(current, (draft) => {
        assert.equal(draft.date.getUTCFullYear(), 2024)
        return draft
      }),
    )

    assert.equal(result, current)
    assert.equal(result.date, dateReference)
  })

  it('allows returning a nested draft proxy as the authoritative root', () => {
    const current = {
      left: { count: 0 },
      right: { count: 0 },
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.left.count = 3
        return draft.left
      }),
    )

    assert.equal<unknown>(result, current)
    assert.deepEqual(result, { count: 3 })
  })

  it('lets an unrelated non-draft return win over draft mutations', () => {
    const current = {
      nested: { count: 0 },
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.nested.count = 5
        return { replace: true as const }
      }),
    )

    assert.equal<unknown>(result, current)
    assert.deepEqual(result, { replace: true })
  })

  it('treats undefined as an ordinary return value', () => {
    const current = { keep: true }

    const result = reconcile(
      current,
      produce<typeof current, undefined>(current, (_draft) => undefined),
    )

    assert.equal(result, undefined)
    assert.deepEqual(current, { keep: true })
  })

  it('publishes incidental primitive returns as ordinary next roots', () => {
    const current = { keep: true }

    assert.equal(
      reconcile(
        current,
        produce(current, (_draft) => 1),
      ),
      1,
    )
    assert.equal(
      reconcile(
        current,
        produce(current, (_draft) => 'patched'),
      ),
      'patched',
    )
    assert.equal(
      reconcile(
        current,
        produce(current, (_draft) => false),
      ),
      false,
    )
    assert.equal(
      reconcile(
        current,
        produce<typeof current, null>(current, (_draft) => null),
      ),
      null,
    )
    assert.deepEqual(current, { keep: true })
  })

  it('publishes returned function values as ordinary atomic roots', () => {
    const current = { keep: true }

    const result = reconcile(
      current,
      produce(current, (_draft) => returnedValue),
    )

    assert.equal(result, returnedValue)
    assert.equal(result(), 'ok')
    assert.deepEqual(current, { keep: true })
  })

  it('uses best-effort fall-through for representative unsupported current surfaces', () => {
    const current = {
      counter: new UnsupportedCounter(1),
    }
    const counterReference = current.counter

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.counter.value = 2
        return draft
      }),
    )

    assert.equal(result, current)
    assert.equal(result.counter, counterReference)
    assert.equal(result.counter instanceof UnsupportedCounter, true)
    assert.equal(result.counter.value, 2)
  })

  it('uses best-effort fall-through for representative unsupported inserted surfaces', () => {
    const inserted = new UnsupportedCounter(3)
    const current = {
      item: 0 as number | UnsupportedCounter,
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.item = inserted
        return draft
      }),
    )

    assert.equal(result, current)
    assert.equal(result.item instanceof UnsupportedCounter, true)
    assert.equal((result.item as UnsupportedCounter).value, 3)
  })

  it('keeps delete distinct from assigning undefined', () => {
    const current: {
      keep: number
      value: number | undefined
      remove?: number
    } = {
      keep: 1,
      remove: 2,
      value: 3,
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        delete draft.remove
        draft.value = undefined
        return draft
      }),
    )

    assert.equal(result, current)
    assert.equal('remove' in result, false)
    assert.equal('value' in result, true)
    assert.equal(result.value, undefined)
  })

  it('creates a present key when assigning undefined to a new object property', () => {
    const current: {
      keep: true
      added?: number | undefined
    } = {
      keep: true,
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.added = undefined
        return draft
      }),
    )

    assert.equal(result, current)
    assert.equal('added' in result, true)
    assert.equal(result.added, undefined)
    assert.deepEqual(Reflect.ownKeys(result), ['keep', 'added'])
  })

  it('treats delete then reassign as an ordinary final present property', () => {
    const current: {
      value?: number | undefined
    } = {
      value: 1,
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        delete draft.value
        draft.value = 2
        return draft
      }),
    )

    assert.equal(result, current)
    assert.equal('value' in result, true)
    assert.equal(result.value, 2)
  })

  it('distinguishes an array hole from a present undefined slot', () => {
    const current = {
      holeList: [10, 20] as Array<number | undefined>,
      undefinedList: [10, 20] as Array<number | undefined>,
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        Reflect.deleteProperty(draft.holeList, 1)
        draft.undefinedList[1] = undefined
        return draft
      }),
    )

    assert.equal(result, current)
    assert.equal(result.holeList.length, 2)
    assert.equal(result.undefinedList.length, 2)
    assert.equal(1 in result.holeList, false)
    assert.equal(1 in result.undefinedList, true)
    assert.equal(result.undefinedList[1], undefined)
  })

  it('directly contrasts delete draft.array[i] with draft.array[i] = undefined', () => {
    const current = {
      assigned: [1, 2, 3] as Array<number | undefined>,
      deleted: [1, 2, 3] as Array<number | undefined>,
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        Reflect.deleteProperty(draft.deleted, 1)
        draft.assigned[1] = undefined
        return draft
      }),
    )

    assert.equal(result, current)
    assert.deepEqual(Object.keys(result.deleted), ['0', '2'])
    assert.deepEqual(Object.keys(result.assigned), ['0', '1', '2'])
    assert.equal(1 in result.deleted, false)
    assert.equal(1 in result.assigned, true)
    assert.equal(result.assigned[1], undefined)
  })

  it('keeps Map delete distinct from setting a key to undefined', () => {
    const current = {
      map: new Map<string, number | undefined>([
        ['drop', 1],
        ['keep', 2],
      ]),
    }
    const mapReference = current.map

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.map.delete('drop')
        draft.map.set('keep', undefined)
        draft.map.set('added', undefined)
        return draft
      }),
    )

    assert.equal(result, current)
    assert.equal(result.map, mapReference)
    assert.equal(result.map.has('drop'), false)
    assert.equal(result.map.has('keep'), true)
    assert.equal(result.map.get('keep'), undefined)
    assert.equal(result.map.has('added'), true)
    assert.equal(result.map.get('added'), undefined)
    assert.deepEqual(Array.from(result.map.keys()), ['keep', 'added'])
  })

  it('treats Map delete then reassign to undefined as an ordinary final present entry', () => {
    const current = {
      map: new Map<string, number | undefined>([['value', 1]]),
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.map.delete('value')
        draft.map.set('value', undefined)
        return draft
      }),
    )

    assert.equal(result.map.has('value'), true)
    assert.equal(result.map.get('value'), undefined)
    assert.deepEqual(Array.from(result.map.keys()), ['value'])
  })

  it('keeps Set delete distinct from adding undefined membership', () => {
    const current = {
      set: new Set<number | undefined>([1, 2]),
    }
    const setReference = current.set

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.set.delete(1)
        draft.set.add(undefined)
        return draft
      }),
    )

    assert.equal(result, current)
    assert.equal(result.set, setReference)
    assert.equal(result.set.has(1), false)
    assert.equal(result.set.has(undefined), true)
    assert.deepEqual(Array.from(result.set.values()), [2, undefined])
  })

  it('treats Set delete then re-add of undefined as an ordinary final present membership', () => {
    const current = {
      // eslint-disable-next-line perfectionist/sort-sets
      set: new Set<number | undefined>([undefined, 1]),
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.set.delete(undefined)
        draft.set.add(undefined)
        return draft
      }),
    )

    assert.equal(result.set.has(undefined), true)
    assert.equal(result.set.size, 2)
    assert.deepEqual(Array.from(result.set.values()), [1, undefined])
  })

  it('preserves repeated draft-originating references coherently', () => {
    const shared = { count: 0 }
    const current = {
      left: shared,
      right: shared,
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.left.count = 2
        return draft
      }),
    )

    assert.equal(result.left, result.right)
    assert.deepEqual(result.left, { count: 2 })
  })

  it('preserves moved draft-originating references at their final locations', () => {
    const current: {
      right: { count: number } | undefined
      left?: { count: number }
    } = {
      left: { count: 0 },
      right: undefined,
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        const moved = draft.left as { count: number }
        delete draft.left
        draft.right = moved
        draft.right.count = 4
        return draft
      }),
    ) as {
      right: { count: number }
      left?: { count: number }
    }

    assert.equal('left' in result, false)
    assert.deepEqual(result.right, { count: 4 })
  })

  it('preserves repeated references across different parents', () => {
    const shared = { count: 0 }
    const current = {
      first: { child: shared },
      second: { child: shared },
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.first.child.count = 5
        return draft
      }),
    )

    assert.equal(result.first.child, result.second.child)
    assert.deepEqual(result.first.child, { count: 5 })
  })

  it('preserves cross-parent sharing when one draft-originating value is kept at multiple final locations', () => {
    const current: {
      left: { count: number }
      right: { count: number } | undefined
      wrapper: { child: { count: number } | undefined }
    } = {
      left: { count: 0 },
      right: undefined,
      wrapper: { child: undefined },
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        const shared = draft.left
        draft.right = shared
        draft.wrapper.child = shared
        shared.count = 6
        return draft
      }),
    ) as {
      left: { count: number }
      right: { count: number }
      wrapper: { child: { count: number } }
    }

    assert.equal(result.left, result.right)
    assert.equal(result.left, result.wrapper.child)
    assert.deepEqual(result.left, { count: 6 })
  })

  it('preserves self-references and cycles after caller publication publication', () => {
    const current: PublicationCyclic = {
      nested: { count: 0 },
    }
    current.self = current

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.nested.count = 7
        return draft
      }),
    )

    assert.equal(result, current)
    assert.equal(result.self, result)
    assert.deepEqual(result.nested, { count: 7 })
  })

  it('allows a formerly shared path to diverge intentionally', () => {
    const shared = { count: 0 }
    const current = {
      left: shared,
      right: shared,
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.left.count = 1
        draft.right = { count: 2 }
        return draft
      }),
    )

    assert.notEqual(result.left, result.right)
    assert.deepEqual(result.left, { count: 1 })
    assert.deepEqual(result.right, { count: 2 })
  })

  it('publishes nested array-element mutations', () => {
    const current = {
      list: [{ count: 0 }],
    }
    const listReference = current.list
    const itemReference = current.list[0]

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.list[0].count = 7
        return draft
      }),
    )

    assert.equal(result, current)
    assert.equal(result.list, listReference)
    assert.equal(result.list[0], itemReference)
    assert.deepEqual(result.list, [{ count: 7 }])
  })

  it('preserves moved draft-originating references between array positions', () => {
    const current = {
      list: [{ count: 0 }, { keep: true }],
    }

    const next = produce(current, (draft) => {
      const moved = draft.list[0] as { count: number }
      draft.list.splice(0, 1)
      draft.list.push(moved)
      moved.count = 8
      return draft
    })
    // The recipe left { keep: true } unchanged, so next holds it at index 0, where current holds
    // the moved object: reconcile would write into it.
    assertWouldChangeNext(current, next)
    const result = reconcile(current, snapshot(next)) as {
      list: Array<{ count: number } | { keep: true }>
    }

    assert.deepEqual(result.list, [{ keep: true }, { count: 8 }])
  })

  it('preserves final placement when moving a draft-originating value into a collection', () => {
    const current: {
      list: Array<{ count: number }>
      item?: { count: number }
    } = {
      item: { count: 0 },
      list: [],
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        const moved = draft.item as { count: number }
        delete draft.item
        draft.list.push(moved)
        moved.count = 9
        return draft
      }),
    )

    assert.equal('item' in result, false)
    assert.deepEqual(result.list, [{ count: 9 }])
  })

  it('preserves final sharing when a moved value still has another final alias', () => {
    const shared = { count: 0 }
    const current: {
      right: { count: number }
      left?: { count: number }
      target?: { child: { count: number } }
    } = {
      left: shared,
      right: shared,
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        const moved = draft.left as { count: number }
        delete draft.left
        draft.target = { child: moved }
        moved.count = 10
        return draft
      }),
    ) as {
      right: { count: number }
      target: { child: { count: number } }
      left?: { count: number }
    }

    assert.equal('left' in result, false)
    assert.equal(result.right, result.target.child)
    assert.deepEqual(result.right, { count: 10 })
  })

  it('supports array mutating methods and preserves holes', () => {
    const current = {
      list: [1, 2, 3] as Array<number | undefined>,
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.list.splice(1, 1)
        Reflect.deleteProperty(draft.list, 1)
        draft.list.push(4)
        return draft
      }),
    )

    assert.equal(result, current)
    assert.equal(result.list.length, 3)
    assert.deepEqual(Object.keys(result.list), ['0', '2'])
    assert.deepEqual(result.list, [1, undefined, 4])
    assert.equal(1 in result.list, false)
  })

  it('finalizes a draft-originating value captured by array push', () => {
    const current = {
      item: { count: 0 },
      list: [] as Array<{ count: number }>,
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.item.count = 11
        draft.list.push(draft.item)
        return draft
      }),
    )

    assert.equal(result.list[0], result.item)
    assert.deepEqual(result.list, [{ count: 11 }])
  })

  it('finalizes a draft-originating value captured by array splice insertion', () => {
    const current = {
      item: { count: 0 },
      list: [{ keep: true }] as Array<{ count: number } | { keep: true }>,
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.item.count = 12
        draft.list.splice(0, 0, draft.item)
        return draft
      }),
    )

    assert.equal(result.list[0], result.item)
    assert.deepEqual(result.list, [{ count: 12 }, { keep: true }])
  })

  it('finalizes a draft-originating value captured as a Map value', () => {
    const current = {
      item: { count: 0 },
      map: new Map<string, { count: number }>(),
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.item.count = 13
        draft.map.set('item', draft.item)
        return draft
      }),
    )

    assert.equal(result.map.get('item'), result.item)
    assert.deepEqual(result.map.get('item'), { count: 13 })
  })

  it('finalizes a draft-originating value captured as a Set value', () => {
    const current = {
      item: { count: 0 },
      set: new Set<object>(),
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.item.count = 14
        draft.set.add(draft.item)
        return draft
      }),
    )

    assert.equal(result.set.size, 1)
    assert.equal(firstSetEntry(result.set), result.item)
    assert.deepEqual(result.item, { count: 14 })
  })

  it('finalizes one draft-originating value captured into multiple collection positions', () => {
    const current = {
      item: { count: 0 },
      list: [] as Array<{ count: number }>,
      map: new Map<string, { count: number }>(),
      set: new Set<object>(),
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.item.count = 15
        draft.list.push(draft.item)
        draft.list.push(draft.item)
        draft.map.set('item', draft.item)
        draft.set.add(draft.item)
        return draft
      }),
    )

    assert.equal(result.list[0], result.item)
    assert.equal(result.list[1], result.item)
    assert.equal(result.map.get('item'), result.item)
    assert.equal(firstSetEntry(result.set), result.item)
    assert.deepEqual(result.item, { count: 15 })
  })

  it('preserves plain-object key order after aligned writes', () => {
    const current = {
      alpha: 1,
      bravo: 2,
      charlie: 3,
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.bravo = 20
        draft.charlie = 30
        return draft
      }),
    )

    assert.equal(result, current)
    assert.deepEqual(Reflect.ownKeys(result), ['alpha', 'bravo', 'charlie'])
    assert.deepEqual(result, {
      alpha: 1,
      bravo: 20,
      charlie: 30,
    })
  })

  it('publishes plain-object key order after divergence and rebuild', () => {
    const current: {
      bravo: number
      charlie: number
      alpha?: number
    } = {
      alpha: 1,
      bravo: 2,
      charlie: 3,
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        delete draft.alpha
        draft.alpha = 10
        return draft
      }),
    )

    assert.equal(result, current)
    assert.deepEqual(Reflect.ownKeys(result), ['bravo', 'charlie', 'alpha'])
    assert.deepEqual(result, {
      alpha: 10,
      bravo: 2,
      charlie: 3,
    })
  })

  it('supports symbol-key participation in retained-root key order', () => {
    const first = Symbol('first')
    const second = Symbol('second')
    const current: {
      alpha: number
      [second]: string
      [first]?: string
    } = {
      alpha: 1,
      [first]: 'first',
      [second]: 'second',
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        delete draft[first]
        draft[first] = 'first-updated'
        return draft
      }),
    ) as {
      alpha: number
      [first]: string
      [second]: string
    }

    assert.equal(result, current)
    assert.deepEqual(Reflect.ownKeys(result), ['alpha', second, first])
    assert.equal(result[first], 'first-updated')
    assert.equal(result[second], 'second')
  })

  it('preserves untouched keys and their identities on retained roots', () => {
    const untouched = { keep: true }
    const current = {
      touched: 0,
      untouched,
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.touched = 1
        return draft
      }),
    )

    assert.equal(result, current)
    assert.equal(result.untouched, untouched)
    assert.deepEqual(result, {
      touched: 1,
      untouched: { keep: true },
    })
  })

  it('removes deleted keys from retained-root plain objects', () => {
    const current: {
      keep: true
      remove?: number
    } = {
      keep: true,
      remove: 1,
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        delete draft.remove
        return draft
      }),
    )

    assert.equal(result, current)
    assert.equal('remove' in result, false)
    assert.deepEqual(Reflect.ownKeys(result), ['keep'])
  })

  it('publishes array length and holes correctly', () => {
    const current = {
      list: [1, 2, 3, 4] as Array<number | undefined>,
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.list.length = 3
        Reflect.deleteProperty(draft.list, 1)
        return draft
      }),
    )

    assert.equal(result, current)
    assert.equal(result.list.length, 3)
    assert.equal(1 in result.list, false)
    assert.deepEqual(Object.keys(result.list), ['0', '2'])
    assert.deepEqual(result.list, [1, undefined, 3])
  })

  it('reindexes arrays correctly for splice', () => {
    const current = {
      list: [1, 2, 3, 4],
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.list.splice(1, 2, 20, 30)
        return draft
      }),
    )

    assert.deepEqual(result.list, [1, 20, 30, 4])
  })

  it('reindexes arrays correctly for shift and unshift', () => {
    const current = {
      list: [2, 3],
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.list.shift()
        draft.list.unshift(1, 2)
        return draft
      }),
    )

    assert.deepEqual(result.list, [1, 2, 3])
  })

  it('reindexes arrays correctly for sort and reverse', () => {
    const current = {
      list: [3, 1, 2],
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.list.sort((left, right) => left - right)
        draft.list.reverse()
        return draft
      }),
    )

    assert.deepEqual(result.list, [3, 2, 1])
  })

  it('supports Map lookup and mutation without drafting keys', () => {
    const current = {
      key: { id: 'key' },
      map: new Map<object, { count: number }>([[{ name: 'fixed-key' }, { count: 0 }]]),
    }
    const [storedKey] = firstMapEntry(current.map)
    const mapReference = current.map

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.map.set(storedKey, { count: 1 })
        draft.map.set(draft.key, { count: 2 })
        const value = draft.map.get(storedKey) as { count: number }
        value.count = 3
        return draft
      }),
    )

    assert.equal(result, current)
    assert.equal(result.map, mapReference)
    assert.equal(result.map.has(storedKey), true)
    assert.deepEqual(result.map.get(storedKey), { count: 3 })
    assert.deepEqual(Array.from(result.map.values()), [{ count: 3 }, { count: 2 }])
  })

  it('publishes final Map order under the supported direct method surface', () => {
    const current = {
      map: new Map<string, number>([
        ['alpha', 1],
        ['bravo', 2],
      ]),
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.map.delete('alpha')
        draft.map.set('charlie', 3)
        draft.map.set('bravo', 20)
        return draft
      }),
    )

    assert.deepEqual(Array.from(result.map.keys()), ['bravo', 'charlie'])
    assert.deepEqual(Array.from(result.map.entries()), [
      ['bravo', 20],
      ['charlie', 3],
    ])
  })

  it('supports Map delete, clear, and size behavior', () => {
    const current = {
      map: new Map<string, number>([
        ['alpha', 1],
        ['bravo', 2],
      ]),
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.map.delete('alpha')
        draft.map.clear()
        draft.map.set('charlie', 3)
        return draft
      }),
    )

    assert.equal(result.map.size, 1)
    assert.deepEqual(Array.from(result.map.entries()), [['charlie', 3]])
  })

  it('publishes draft-originating map keys coherently with ordinary object paths', () => {
    const key = { label: 'key' }
    const current = {
      key,
      map: new Map<object, number>([[key, 1]]),
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.key.label = 'updated'
        assert.equal(current.key.label, 'key')
        assert.equal(draft.map.get(draft.key), 1)
        draft.map.set(draft.key, 2)
        return draft
      }),
    )

    const [resultKey] = firstMapEntry(result.map)
    assert.equal(resultKey, result.key)
    assert.equal(resultKey, current.key)
    assert.equal((resultKey as { label: string }).label, 'updated')
    assert.equal(result.map.get(result.key), 2)
    assert.equal(result.key.label, 'updated')
  })

  it('publishes final Map key iteration order while finalizing draft-originating keys coherently', () => {
    const key = { label: 'key' }
    const trailingKey = { trailing: true }
    const current = {
      key,
      map: new Map<object, number>([
        [key, 1],
        [trailingKey, 9],
      ]),
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.key.label = 'updated'
        draft.map.delete(draft.key)
        draft.map.set(draft.key, 2)
        draft.map.set({ extra: true }, 3)
        return draft
      }),
    )

    const resultKeys = Array.from(result.map.keys())

    assert.equal(resultKeys.length, 3)
    assert.deepEqual(resultKeys[0], { trailing: true })
    assert.notEqual(resultKeys[0], result.key)
    assert.equal(resultKeys[1], result.key)
    assert.equal(resultKeys[1], current.key)
    assert.equal((resultKeys[1] as { label: string }).label, 'updated')
    assert.deepEqual(Array.from(result.map.values()), [9, 2, 3])
  })

  it('rejects a nested Map return that cannot replace an ordinary object root', () => {
    const key = { label: 'key' }
    const current = { key, map: new Map<object, number>([[key, 1]]) }
    assert.throws(
      () =>
        reconcile(
          current,
          produce(current, (draft) => {
            draft.key.label = 'updated'
            return draft.map
          }),
        ),
      ReconcileError,
    )
    assert.equal(current.key.label, 'key')
  })

  it('publishes Date map keys coherently at the publication boundary', () => {
    const key = new Date('2024-01-01T00:00:00.000Z')
    const current = {
      key,
      map: new Map<Date, number>([[key, 1]]),
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.key.setUTCFullYear(2025)
        assert.equal(current.key.getUTCFullYear(), 2024)
        draft.map.set(draft.key, 2)
        return draft
      }),
    )

    const [resultKey] = firstMapEntry(result.map)

    assert.equal(result, current)
    assert.equal(resultKey, result.key)
    assert.equal(resultKey, current.key)
    assert.equal(resultKey.getUTCFullYear(), 2025)
    assert.equal(result.map.get(current.key), 2)
  })

  it('publishes ArrayBuffer map keys coherently at the publication boundary', () => {
    const key = new Uint8Array([1, 2, 3]).buffer
    const current = {
      key,
      map: new Map<ArrayBuffer, number>([[key, 1]]),
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        new Uint8Array(draft.key)[0] = 9
        assert.deepEqual(bytesOf(current.key), [1, 2, 3])
        draft.map.set(draft.key, 2)
        return draft
      }),
    )

    const [resultKey] = firstMapEntry(result.map)

    assert.equal(result, current)
    assert.equal(resultKey, result.key)
    assert.equal(resultKey, current.key)
    assert.deepEqual(bytesOf(resultKey), [9, 2, 3])
    assert.equal(result.map.get(current.key), 2)
  })

  it('supports Set add/delete/has/size with collection-local preparation', () => {
    const item = { count: 0 }
    const current = {
      item,
      set: new Set<object>([item]),
    }
    const setReference = current.set

    const result = reconcile(
      current,
      produce(current, (draft) => {
        assert.equal(draft.set.has(draft.item), true)
        draft.set.delete(draft.item)
        assert.equal(draft.set.has(draft.item), false)
        draft.item.count = 2
        draft.set.add(draft.item)
        assert.equal(draft.set.size, 1)
        return draft
      }),
    )

    assert.equal(result, current)
    assert.equal(result.set, setReference)
    assert.equal(result.set.size, 1)
    assert.equal(firstSetEntry(result.set), result.item)
    assert.deepEqual(result.item, { count: 2 })
  })

  it('publishes final Set order under the supported direct method surface', () => {
    const current = {
      set: new Set<number>([1, 2, 3]),
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.set.delete(2)
        draft.set.add(4)
        draft.set.delete(1)
        draft.set.add(1)
        return draft
      }),
    )

    assert.deepEqual(Array.from(result.set.values()), [3, 4, 1])
  })

  it('supports Set clear, delete, and size behavior', () => {
    const current = {
      set: new Set<number>([1, 2, 3]),
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.set.delete(1)
        draft.set.clear()
        draft.set.add(4)
        draft.set.add(5)
        return draft
      }),
    )

    assert.equal(result.set.size, 2)
    assert.deepEqual(Array.from(result.set.values()), [4, 5])
  })

  it('keeps Set collection-local preparation coherent for membership and order', () => {
    const item = { count: 0 }
    const other = { keep: true }
    const current = {
      item,
      other,
      // eslint-disable-next-line perfectionist/sort-sets
      set: new Set<object>([other, item]),
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        assert.equal(draft.set.has(draft.item), true)
        draft.set.delete(draft.item)
        assert.equal(draft.set.has(draft.item), false)
        draft.item.count = 16
        draft.set.add(draft.item)
        assert.equal(draft.set.has(draft.item), true)
        return draft
      }),
    ) as {
      item: { count: number }
      other: { keep: true }
      set: Set<object>
    }

    assert.deepEqual(Array.from(result.set.values()), [result.other, result.item])
    assert.equal(result.set.has(result.item), true)
    assert.deepEqual(result.item, { count: 16 })
  })

  it('applies changes made while iterating Map and Set drafts', () => {
    const current = {
      map: new Map([['a', { n: 1 }]]),
      set: new Set([{ n: 1 }]),
    }
    const map = current.map
    const entry = current.map.get('a')!
    reconcile(
      current,
      produce(current, (draft) => {
        for (const [, value] of draft.map) value.n = 2
        draft.set.forEach((member) => {
          member.n = 3
        })
        return draft
      }),
    )
    assert.strictEqual(current.map, map)
    assert.strictEqual(current.map.get('a'), entry)
    assert.equal(entry.n, 2)
    assert.deepEqual([...current.set], [{ n: 3 }])
  })

  it('supports Date mutation through clone-on-read semantics', () => {
    const current = {
      date: new Date('2024-01-01T00:00:00.000Z'),
    }
    const dateReference = current.date

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.date.setUTCFullYear(2025)
        return draft
      }),
    )

    assert.equal(result, current)
    assert.equal(result.date, dateReference)
    assert.equal(result.date.getUTCFullYear(), 2025)
  })

  it('preserves buffer and view aliasing when a typed array draft clone is mutated', () => {
    const buffer = new Uint8Array([1, 2, 3, 4]).buffer
    const current = {
      buffer,
      typed: new Uint8Array(buffer),
      view: new DataView(buffer),
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.typed[1] = 9
        return draft
      }),
    )

    assert.equal(result.typed.buffer, result.buffer)
    assert.equal(result.view.buffer, result.buffer)
    assert.deepEqual(Array.from(new Uint8Array(result.buffer)), [1, 9, 3, 4])
    assert.deepEqual(Array.from(result.typed), [1, 9, 3, 4])
    assert.deepEqual(
      Array.from(
        new Uint8Array(result.view.buffer, result.view.byteOffset, result.view.byteLength),
      ),
      [1, 9, 3, 4],
    )
  })

  it('preserves aliasing for multiple views into one next-side buffer', () => {
    const buffer = new Uint8Array([1, 2, 3, 4]).buffer
    const current = {
      left: new Uint8Array(buffer, 0, 2),
      right: new DataView(buffer, 2, 2),
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.left[0] = 7
        return draft
      }),
    )

    assert.equal(result.left.buffer, result.right.buffer)
    assert.deepEqual(Array.from(result.left), [7, 2])
    assert.deepEqual(
      Array.from(
        new Uint8Array(result.right.buffer, result.right.byteOffset, result.right.byteLength),
      ),
      [3, 4],
    )
    assert.deepEqual(Array.from(new Uint8Array(result.left.buffer)), [7, 2, 3, 4])
  })

  it('preserves aliasing when a DataView draft clone is mutated', () => {
    const buffer = new Uint8Array([1, 2, 3, 4]).buffer
    const current = {
      typed: new Uint8Array(buffer),
      view: new DataView(buffer),
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.view.setUint8(2, 8)
        return draft
      }),
    )

    assert.equal(result.typed.buffer, result.view.buffer)
    assert.deepEqual(Array.from(result.typed), [1, 2, 8, 4])
    assert.deepEqual(
      Array.from(
        new Uint8Array(result.view.buffer, result.view.byteOffset, result.view.byteLength),
      ),
      [1, 2, 8, 4],
    )
  })

  it('preserves one coherent next-side buffer across mixed typed-array and DataView replacement cases', () => {
    const current = {
      typed: new Uint8Array(new Uint8Array([9, 9, 9, 9]).buffer),
      view: new DataView(new Uint8Array([5, 6, 7, 8]).buffer),
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.typed[1] = 10
        return {
          typed: new Uint16Array(draft.typed.buffer),
          view: new DataView(draft.typed.buffer, 1, 2),
        }
      }),
    ) as {
      typed: Uint16Array
      view: DataView
    }

    assert.equal(result.typed.buffer, result.view.buffer)
    assert.equal(result.typed.constructor, Uint16Array)
    assert.deepEqual(Array.from(new Uint8Array(result.typed.buffer)), [9, 10, 9, 9])
    assert.deepEqual(
      Array.from(
        new Uint8Array(result.view.buffer, result.view.byteOffset, result.view.byteLength),
      ),
      [10, 9],
    )
  })

  it('preserves fresh detached buffer/view child subtrees when finalization returns a detached root shape', () => {
    const current = {
      typed: new Uint8Array(new Uint8Array([1, 2, 3, 4]).buffer),
      view: new DataView(new Uint8Array([5, 6, 7, 8]).buffer),
    }
    const typedReference = current.typed
    const viewReference = current.view

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.typed[0] = 11
        return {
          typed: new Uint16Array(draft.typed.buffer),
          view: new DataView(draft.typed.buffer, 2, 2),
        }
      }),
    ) as {
      typed: Uint16Array
      view: DataView
    }

    assert.equal<unknown>(result, current)
    assert.notEqual<unknown>(result.typed, typedReference)
    assert.notEqual(result.view, viewReference)
    assert.equal(result.typed.buffer, result.view.buffer)
    assert.equal(result.typed.constructor, Uint16Array)
    assert.deepEqual(Array.from(new Uint8Array(result.typed.buffer)), [11, 2, 3, 4])
    assert.deepEqual(
      Array.from(
        new Uint8Array(result.view.buffer, result.view.byteOffset, result.view.byteLength),
      ),
      [3, 4],
    )
  })

  it('sanitizes caller publication-owned drafts nested inside an ordinary returned root', () => {
    const current = {
      nested: { count: 0 },
    }

    const result = reconcile(
      current,
      produce(current, (draft) => {
        draft.nested.count = 6
        return { wrapped: draft.nested }
      }),
    )

    assert.equal<unknown>(result, current)
    assert.deepEqual(result, { wrapped: { count: 6 } })
  })
})
