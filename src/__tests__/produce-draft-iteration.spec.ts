import { assert, describe, it } from 'vitest'
import { reactive, shallowReadonly, toRaw } from 'vue'
import { produce } from '../index'

// A Map or Set draft iterates its working copy natively: object values come back as drafts, writes
// made during the walk change the walked collection as on a native Map or Set, and an iteration
// that changes nothing keeps the original. lean/Produce/DraftIteration.lean proves the rules and
// check-draft-iteration-runtime.ts compares them natively.

describe('Map and Set drafts iterate like native collections', () => {
  it('yields drafts of object values through every iteration API', () => {
    const current = { map: new Map([['a', { n: 1 }]]), set: new Set([{ n: 1 }]) }
    const result = produce(current, (draft) => {
      for (const [key, value] of draft.map) if (key === 'a') value.n += 1
      for (const value of draft.map.values()) value.n += 1
      draft.map.forEach((value) => {
        value.n += 1
      })
      for (const [member] of draft.set.entries()) member.n += 1
      return draft
    })
    assert.equal(result.map.get('a')!.n, 4)
    assert.equal([...result.set][0].n, 2)
    assert.equal(current.map.get('a')!.n, 1)
    assert.equal([...current.set][0].n, 1)
  })

  it('keeps the original when an iteration changes nothing', () => {
    const current = { map: new Map([['a', { n: 1 }]]), set: new Set([1, 2]) }
    const result = produce(current, (draft) => {
      void [...draft.map.keys(), ...draft.map.values(), ...draft.set]
      return draft
    })
    assert.strictEqual(result, current)
  })

  it('sees writes made during the walk as a native Map does', () => {
    const script = (map: Map<string, number>): string[] => {
      const seen: string[] = []
      for (const [key, value] of map) {
        seen.push(`${key}=${value}`)
        if (key === 'a') {
          map.delete('b')
          map.set('c', 3)
          map.set('a', 9)
        }
      }
      return seen
    }
    const native = new Map([
      ['a', 1],
      ['b', 2],
    ])
    const expected = script(new Map(native))
    let seen: string[] = []
    const result = produce({ map: native }, (draft) => {
      seen = script(draft.map)
      return draft
    })
    assert.deepEqual(seen, expected)
    assert.deepEqual(
      [...result.map],
      [
        ['a', 9],
        ['c', 3],
      ],
    )
    assert.deepEqual(
      [...native],
      [
        ['a', 1],
        ['b', 2],
      ],
    )
  })

  it('copies a draft Map or Set through its iterator', () => {
    const current = { map: new Map([['a', { n: 1 }]]) }
    const result = produce(current, (draft) => ({
      copy: new Map(draft.map),
      keys: [...draft.map.keys()],
    }))
    assert.strictEqual(result.copy.get('a'), current.map.get('a'))
    assert.deepEqual(result.keys, ['a'])
  })

  it('iterates a Vue reactive Map draft without changing the state', () => {
    const state = reactive({ map: new Map([['a', { n: 1 }]]) })
    const result = produce(state, (draft) => {
      for (const value of draft.map.values()) value.n = 2
      return draft
    })
    assert.equal(result.map.get('a')!.n, 2)
    assert.equal(toRaw(state).map.get('a')!.n, 1)
  })
})

// Lists a Set's members with each draft replaced by its original, for comparison with native.
function originals(set: Set<unknown>, drafts: Map<unknown, unknown>): unknown[] {
  return [...set].map((member) => drafts.get(member) ?? member)
}

describe('Set drafts combine and compare like native Sets', () => {
  const combinations = ['union', 'intersection', 'difference', 'symmetricDifference'] as const
  const comparisons = ['isSubsetOf', 'isSupersetOf', 'isDisjointFrom'] as const
  const shared = { n: 1 }
  const own = { n: 2 }
  const other = { n: 3 }

  for (const operand of ['native', 'draft', 'mixed'] as const)
    it(`matches native results with a ${operand} operand`, () => {
      // Insertion order matters to the native results, so the members are listed in that order.
      const leftMembers: unknown[] = [shared, own, 1]
      const rightMembers: unknown[] = [shared, other, 2]
      const left = new Set(leftMembers)
      const right = new Set(rightMembers)
      produce({ left, right }, (draft) => {
        const drafts = new Map<unknown, unknown>()
        for (const member of draft.left) drafts.set(member, [...left][drafts.size])
        const argument =
          operand === 'native'
            ? right
            : operand === 'draft'
              ? draft.right
              : new Set([...draft.right])
        if (operand !== 'native')
          for (const [index, member] of [...draft.right].entries())
            drafts.set(member, [...right][index])
        for (const method of combinations)
          assert.deepEqual(
            originals(draft.left[method](argument), drafts),
            [...left[method](right)],
            method,
          )
        for (const method of comparisons)
          assert.equal(draft.left[method](argument), left[method](right), method)
        return draft
      })
    })

  it('counts a Vue reactive member and its raw object as one member', () => {
    const member = { n: 1 }
    const members: object[] = [member, { n: 2 }]
    const state = reactive({ tags: new Set(members) })
    produce(state, (draft) => {
      // eslint-disable-next-line baseline-js/use-baseline -- the draft's own Set methods
      assert.equal(draft.tags.intersection(new Set([member])).size, 1)
      // eslint-disable-next-line baseline-js/use-baseline -- the draft's own Set methods
      assert.isTrue(draft.tags.isSupersetOf(new Set([member])))
      return draft
    })
  })

  it('returns object members as their drafts, so a change through one is kept', () => {
    const current = { tags: new Set([{ n: 1 }]) }
    const result = produce(current, (draft) => {
      // eslint-disable-next-line baseline-js/use-baseline -- the draft's union, which runs on any engine with Set methods
      for (const member of draft.tags.union(new Set())) (member as { n: number }).n = 2
      return draft
    })
    assert.deepEqual([...result.tags], [{ n: 2 }])
    assert.deepEqual([...current.tags], [{ n: 1 }])
  })
})

/** Runs `method` with an operand that adds and removes members of `set` while it is asked. */
function runChanging(set: Set<number>, method: 'difference' | 'intersection'): unknown[] {
  const calls: unknown[] = []
  const operand = {
    has(value: number) {
      calls.push(value)
      if (value === 1) set.delete(2)
      if (value === 3) set.add(9)
      return value !== 3
    },
    keys: () => [][Symbol.iterator](),
    get size() {
      calls.push('size')
      return 10
    },
  }
  return [[...set[method](operand)], calls, [...set]]
}

/* eslint-disable baseline-js/use-baseline -- the draft's own Set methods, compared with native ones */
describe('Set draft methods follow the native algorithms', () => {
  it('reads a Set from current as its own members, not as the draft', () => {
    const current = { tags: new Set(['a', 'b']) }
    produce(current, (draft) => {
      draft.tags.add('c')
      draft.tags.delete('a')
      assert.deepEqual([...draft.tags.difference(current.tags)], ['c'])
      assert.isFalse(draft.tags.isSubsetOf(current.tags))
      return draft
    })
  })

  it('finds an object member in a native Set or Map in any of its forms', () => {
    const member = { n: 1 }
    const current = { tags: new Set([member]) }
    produce(current, (draft) => {
      const [drafted] = draft.tags
      assert.isTrue(draft.tags.isSubsetOf(new Set([member])))
      assert.isTrue(draft.tags.isSubsetOf(new Set([drafted])))
      assert.equal(draft.tags.intersection(new Map([[drafted, 1]])).size, 1)
      return draft
    })
  })

  it("asks a set-like operand's own has with drafts, so it cannot change current", () => {
    const member = { n: 1 }
    const current = { tags: new Set([member]) }
    const seen: unknown[] = []
    const result = produce(current, (draft) => {
      draft.tags.isSubsetOf({
        size: 1,
        has(value: { n: number }) {
          seen.push(value)
          value.n = 2
          return true
        },
        keys: () => [][Symbol.iterator](),
      })
      return draft
    })
    assert.notEqual(seen[0], member)
    assert.equal(member.n, 1)
    assert.deepEqual([...result.tags], [{ n: 2 }])
  })

  it('walks the smaller side and stops where the native method stops', () => {
    const calls: string[] = []
    const operand = {
      size: 1,
      has: () => {
        calls.push('has')
        return true
      },
      keys: () => {
        calls.push('keys')
        return [1][Symbol.iterator]()
      },
    }
    const members = Array.from({ length: 1000 }, (_, index) => index)
    produce({ numbers: new Set(members) }, (draft) => {
      assert.deepEqual([...draft.numbers.intersection(operand)], [1])
      assert.isFalse(draft.numbers.isDisjointFrom(operand))
      assert.deepEqual(calls, ['keys', 'keys'])
      return draft
    })
  })

  it('sees members the operand adds or removes, as natively', () => {
    for (const method of ['difference', 'intersection'] as const)
      produce({ numbers: new Set([1, 2, 3]) }, (draft) => {
        assert.deepEqual(
          runChanging(draft.numbers, method),
          runChanging(new Set([1, 2, 3]), method),
          method,
        )
        return draft
      })
  })

  it("runs a subclass's override and an operand's own has", () => {
    class Tags extends Set<unknown> {
      override union<U>(other: ReadonlySetLike<U>): Set<unknown> {
        return new Set(['override', ...super.union(other)])
      }
    }
    class Folded extends Set<string> {
      override has(value: string): boolean {
        return super.has(value.toLowerCase())
      }
    }
    produce({ plain: new Set(['A']), tags: new Tags(['a']) }, (draft) => {
      assert.deepEqual([...draft.tags.union(new Set())], ['override', 'a'])
      assert.isTrue(draft.plain.isSubsetOf(new Folded(['a'])))
      return draft
    })
  })

  it('counts a Vue proxy as its raw object only in Vue reactive state', () => {
    const member = { n: 1 }
    const proxy = reactive(member)
    produce({ tags: new Set([member]) }, (draft) => {
      assert.isFalse(draft.tags.has(proxy))
      assert.equal(draft.tags.intersection(new Set([proxy])).size, 0)
      return draft
    })
    produce(reactive({ tags: new Set([member]) }), (draft) => {
      assert.isTrue(draft.tags.has(proxy))
      assert.equal(draft.tags.intersection(new Set([proxy])).size, 1)
      return draft
    })
  })
})
/* eslint-enable baseline-js/use-baseline */

describe('Map and Set draft iterators behave like native iterators', () => {
  it('stay open after a loop leaves early and report their native kind', () => {
    produce(
      {
        map: new Map([
          [1, 'a'],
          [2, 'b'],
        ]),
        set: new Set([1, 2, 3]),
      },
      (draft) => {
        const values = draft.set.values()
        // eslint-disable-next-line no-unreachable-loop -- a loop that leaves after one value
        for (const _ of values) break
        assert.deepEqual([...values], [2, 3])
        const [first] = draft.map.entries()
        assert.deepEqual(first, [1, 'a'])
        assert.equal(Object.prototype.toString.call(draft.set.values()), '[object Set Iterator]')
        assert.equal(Object.prototype.toString.call(draft.map.entries()), '[object Map Iterator]')
        assert.deepEqual(Object.keys(draft.set.values().next()), ['value', 'done'])
        return draft
      },
    )
  })

  it('run a subclass override where it runs natively', () => {
    const calls: string[] = []
    class Tags extends Set<number> {
      override forEach(...parameters: Parameters<Set<number>['forEach']>): void {
        calls.push('forEach')
        super.forEach(...parameters)
      }
      override keys(): SetIterator<number> {
        calls.push('keys')
        return super.keys()
      }
      override values(): SetIterator<number> {
        calls.push('values')
        return super.values()
      }
    }
    class Entries extends Map<number, number> {
      override entries(): MapIterator<[number, number]> {
        calls.push('entries')
        return super.entries()
      }
    }
    const run = (tags: Set<number>, entries: Map<number, number>) => {
      calls.length = 0
      tags.forEach(() => undefined)
      for (const _ of tags);
      for (const _ of entries);
      void [...tags.keys(), ...entries.entries()]
      return [...calls]
    }
    const native = run(new Tags([1]), new Entries([[1, 1]]))
    produce({ entries: new Entries([[1, 1]]), tags: new Tags([1]) }, (draft) => {
      assert.deepEqual(run(draft.tags, draft.entries), native)
      return draft
    })
    assert.deepEqual(native, ['forEach', 'keys', 'entries'])
  })

  it('check the forEach callback before walking, as natively', () => {
    produce({ map: new Map(), set: new Set() }, (draft) => {
      assert.throws(() => draft.map.forEach(1 as never), TypeError)
      assert.throws(() => draft.set.forEach(1 as never), TypeError)
      assert.equal(draft.map.forEach.length, 1)
      return draft
    })
  })
})

/* eslint-disable baseline-js/use-baseline -- the draft's own Set methods, compared with native ones */
describe('Set draft methods keep native results in corner cases', () => {
  it('find an undefined member in a native operand', () => {
    const operand = new Set([1, undefined])
    produce({ members: new Set([undefined]) }, (draft) => {
      assert.isTrue(draft.members.isSubsetOf(operand))
      assert.deepEqual([...draft.members.intersection(operand)], [undefined])
      return draft
    })
  })

  it("read members and size as the native methods do, past a subclass's overrides", () => {
    class Hidden extends Set<unknown> {
      override get size(): number {
        return 0
      }
      override *[Symbol.iterator](): SetIterator<unknown> {
        yield 'fake'
      }
    }
    const operand = { size: 1, has: () => true, keys: () => [1][Symbol.iterator]() }
    const run = (set: Set<unknown>) => [
      [...Set.prototype.values.call(set.difference(new Set()))],
      [...Set.prototype.values.call(set.intersection(operand))],
    ]
    const native = run(new Hidden([1, 2]))
    produce({ hidden: new Hidden([1, 2]) }, (draft) => {
      assert.deepEqual(run(draft.hidden), native)
      return draft
    })
  })

  it("give a subclass override's result members as drafts and keep its writes", () => {
    class Tagged extends Set<unknown> {
      override union<U>(other: ReadonlySetLike<U>): Set<unknown> {
        this.add('side')
        return new Set([...Set.prototype.values.call(this), ...Set.prototype.values.call(other)])
      }
    }
    const member = { n: 1 }
    const current = { tags: new Tagged([member]) }
    const result = produce(current, (draft) => {
      for (const value of draft.tags.union(new Set()))
        if (typeof value === 'object' && value !== null) (value as { n: number }).n = 2
      return draft
    })
    assert.equal(member.n, 1)
    assert.deepEqual([...Set.prototype.values.call(result.tags)], [{ n: 2 }, 'side'])
  })

  it('find a member added in Vue reactive state after a walk', () => {
    const first = { n: 1 }
    const second = { n: 2 }
    produce(reactive({ tags: new Set<object>([first]) }), (draft) => {
      for (const _ of draft.tags);
      draft.tags.delete(first)
      draft.tags.add(shallowReadonly(second))
      assert.isTrue(draft.tags.has(second))
      assert.isTrue(draft.tags.isSupersetOf(new Set([second])))
      return draft
    })
  })
})
/* eslint-enable baseline-js/use-baseline */

describe('Map drafts walk entries as the built-in iterator does', () => {
  it("copies every entry, past a subclass's iterator", () => {
    class Hiding extends Map<string, number> {
      override *[Symbol.iterator](): MapIterator<[string, number]> {
        for (const entry of Map.prototype.entries.call(this)) if (entry[0] !== 'hidden') yield entry
      }
    }
    const current = {
      map: new Hiding([
        ['a', 1],
        ['hidden', 2],
      ]),
    }
    const result = produce(current, (draft) => {
      draft.map.set('b', 3)
      return draft
    })
    assert.deepEqual(
      [...Map.prototype.entries.call(result.map)],
      [
        ['a', 1],
        ['hidden', 2],
        ['b', 3],
      ],
    )
  })
})

describe('draft iterators end as for...of ends them', () => {
  it('end on a truthy done from a subclass iterator', () => {
    class Ending extends Set<unknown> {
      override values(): SetIterator<unknown> {
        const values = Set.prototype.values.call(this)
        return Object.assign(Object.create(Object.getPrototypeOf(values) as object) as object, {
          next: () => {
            const step = values.next()
            return step.done === true ? { done: 1, value: 'end' } : step
          },
        }) as SetIterator<unknown>
      }
    }
    produce({ set: new Ending([1, 2]) }, (draft) => {
      assert.deepEqual([...draft.set.values()], [...new Ending([1, 2]).values()])
      return draft
    })
  })
})

/* eslint-disable baseline-js/use-baseline -- the draft's own Set methods, compared with native ones */
describe("a subclass's own Set method", () => {
  it('never changes the set it returns', () => {
    class Passing extends Set<unknown> {
      override union<U>(other: ReadonlySetLike<U>): Set<unknown> {
        return other as unknown as Set<unknown>
      }
    }
    const member = { n: 1 }
    const outside = new Set([member])
    const current = { other: new Set([member]), tags: new Passing([member]) }
    produce(current, (draft) => {
      assert.equal(draft.tags.union(outside), outside)
      assert.equal(draft.tags.union(current.other), current.other)
      assert.equal(draft.tags.union(draft.other), draft.other)
      return draft
    })
    assert.deepEqual([...outside], [member])
    assert.deepEqual([...current.other], [member])
  })

  it('keeps a set of its own class as the override built it', () => {
    class Labelled extends Set<unknown> {
      readonly #label: string
      constructor(members?: Iterable<unknown>, label = 'none') {
        super(members)
        this.#label = label
      }
      label(): string {
        return this.#label
      }
      override union<U>(other: ReadonlySetLike<U>): Set<unknown> {
        return new Labelled(super.union(other), 'union')
      }
    }
    produce({ tags: new Labelled([{ n: 1 }]) }, (draft) => {
      assert.equal((draft.tags.union(new Set([1])) as Labelled).label(), 'union')
      return draft
    })
  })

  it('walk a subclass instance with an own iterator as the built-in methods do', () => {
    class Tags extends Set<unknown> {}
    class Index extends Map<unknown, unknown> {}
    const tags = new Tags([1, 2])
    const map = new Index([[1, 1]])
    Object.defineProperty(tags, Symbol.iterator, { value: () => ['junk'][Symbol.iterator]() })
    Object.defineProperty(map, Symbol.iterator, { value: () => [['junk', 0]][Symbol.iterator]() })
    const result = produce({ map, tags }, (draft) => {
      draft.tags.add(3)
      draft.map.set(2, 2)
      return draft
    })
    assert.deepEqual([...Set.prototype.values.call(result.tags)], [1, 2, 3])
    assert.deepEqual(
      [...Map.prototype.entries.call(result.map)],
      [
        [1, 1],
        [2, 2],
      ],
    )
  })
})
/* eslint-enable baseline-js/use-baseline */

/** A proxy that binds the methods it gives to its target, as some wrappers do. */
const bind = <T extends object>(target: T): T =>
  new Proxy(target, {
    get(object, key) {
      const value = Reflect.get(object, key, object) as unknown
      return typeof value === 'function' ? (value as () => unknown).bind(object) : value
    },
  })

describe('Map and Set subclass drafts', () => {
  it('keep a proxy that binds methods to its Set or Map working', () => {
    class Tags extends Set<unknown> {}
    class Index extends Map<unknown, unknown> {}
    const result = produce(
      { index: bind(new Index([[1, 1]])), other: { n: 1 }, tags: bind(new Tags([1])) },
      (draft) => {
        draft.other.n = 2
        draft.index.set(2, 2)
        draft.tags.add(2)
        return draft
      },
    )
    assert.deepEqual(
      [...result.index],
      [
        [1, 1],
        [2, 2],
      ],
    )
    assert.deepEqual([...result.tags], [1, 2])
  })

  it("decide membership with the built-in has, as the built-in methods do, past a subclass's", () => {
    class Folded extends Set<string> {
      override has(value: string): boolean {
        return super.has(value.toLowerCase())
      }
    }
    const result = produce({ letters: new Folded(['a']) }, (draft) => {
      draft.letters.add('A')
      assert.isTrue(draft.letters.has('A'))
      return draft
    })
    assert.deepEqual([...result.letters], ['a', 'A'])
  })

  it("keep a subclass's writes whatever its delete returns", () => {
    class Quiet extends Set<number> {
      override delete(value: number): boolean {
        super.delete(value)
        return false
      }
    }
    const current = { numbers: new Quiet([1, 2]) }
    const result = produce(current, (draft) => {
      draft.numbers.delete(1)
      return draft
    })
    assert.notEqual(result, current)
    assert.deepEqual([...result.numbers], [2])
  })

  it("find keys a subclass's set adds in Vue reactive state", () => {
    const first = { n: 1 }
    const derived = { n: 2 }
    class Linked extends Map<object, unknown> {
      override set(key: object, value: unknown): this {
        if (this.size === 1) super.set(derived, 'derived')
        return super.set(key, value)
      }
    }
    produce(reactive({ links: new Linked([[first, 1]]) }), (draft) => {
      for (const _ of draft.links);
      draft.links.set(first, 2)
      assert.equal(draft.links.get(reactive(derived)), 'derived')
      return draft
    })
  })
})
