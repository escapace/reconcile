import { builtinTypes } from '../types/builtins'
import { atomValue, isNode } from '../graph/edge'
import { describe, expect, it } from 'vitest'
import { capture } from '../publication/capture'
import { candidates } from '../publication/candidates'

function problem(current: object, next: object) {
  const records = capture(builtinTypes, next).nodes
  return { domains: candidates(builtinTypes, records, current), records }
}

describe('native candidate discovery', () => {
  it('compiles fixed cycles and shared references without deciding or writing input', () => {
    const child = { n: 0 }
    const current = { child, self: {} }
    current.self = current
    Object.freeze(current)
    const next = { child: { n: 1 }, self: {} }
    next.self = next
    const { domains } = problem(current, next)
    expect(domains.map((domain) => domain.map((choice) => choice.identity))).toEqual([
      [current],
      [child],
    ])
    expect(domains[0][0].required).toEqual([
      { identity: child, node: 1 },
      { identity: current, node: 0 },
    ])
    expect(child.n).toBe(0)
  })

  it('rejects incompatible fixed identities and own surfaces before publication', () => {
    const shared = { n: 1 }
    const cases: Array<[object, object]> = [
      [Object.freeze({ left: {}, right: {} }), { left: shared, right: shared }],
      [Object.preventExtensions({ n: 0 }), { added: 2, n: 1 }],
      [Object.freeze({ n: 0 }), { n: 1 }],
      [new ArrayBuffer(1), new ArrayBuffer(2)],
    ]
    for (const [current, next] of cases) expect(problem(current, next).domains[0]).toEqual([])
  })

  it('offers a frozen root whose fixed slots hold one object at two positions', () => {
    const shared = { n: 1 }
    const { domains } = problem(Object.freeze({ left: shared, right: shared }), {
      left: {},
      right: {},
    })
    // The root requires both nodes to keep `shared`, which the decision then cannot establish.
    expect(domains[0][0].required).toEqual([
      { identity: shared, node: 1 },
      { identity: shared, node: 2 },
    ])
  })

  it('binds a view to its buffer through one conditional rule', () => {
    const first = new ArrayBuffer(4)
    const second = new ArrayBuffer(4)
    const view = new Uint8Array(second)
    const nextBuffer = new ArrayBuffer(4)
    const { domains } = problem(
      { a: first, b: second, view },
      { a: nextBuffer, b: nextBuffer, view: new Uint8Array(nextBuffer) },
    )
    expect(domains[1].map((choice) => choice.identity)).toEqual([first, second])
    expect(domains[2]).toEqual([{ identity: view, required: [{ identity: second, node: 1 }] }])
  })

  it('preserves compatible children when a fixed parent candidate cannot be retained', () => {
    const child = { n: 0 }
    const parent = Object.freeze({ child, obsolete: 1 })
    const { domains } = problem({ parent }, { parent: { child: { n: 2 } } })
    expect(domains[1]).toEqual([])
    expect(domains[2][0].identity).toBe(child)
    expect(child.n).toBe(0)
  })
  it('aligns Map entries from the built-in contents, never through an own entries method', () => {
    const child = { n: 0 }
    const events: string[] = []
    const entry: [string, object] = ['key', child]
    Object.defineProperties(entry, {
      0: {
        get() {
          events.push('key')
          return 'key'
        },
      },
      1: {
        get() {
          events.push('value')
          return child
        },
      },
    })
    const current = new Map([['key', child]])
    current.entries = function* () {
      yield entry as [string, typeof child]
      return undefined
    }
    const { domains } = problem(current, new Map([['key', { n: 1 }]]))
    expect(events).toEqual([])
    expect(domains[1][0].identity).toBe(child)
  })
  it('reads collection sizes with the built-in getter, never an own size', () => {
    for (const current of [new Map([['key', 1]]), new Set(['key'])]) {
      const node = capture(builtinTypes, current).nodes[0]
      let coercions = 0
      Object.defineProperty(current, 'size', {
        value: {
          valueOf() {
            coercions += 1
            return 1
          },
        },
      })
      expect(
        builtinTypes.policies[node.layout.kind].matches(
          node,
          current,
          (actual, edge) => !isNode(edge) && Object.is(actual, atomValue(edge)),
        ),
      ).toBe(true)
      expect(coercions).toBe(0)
    }
  })
  it('returns ordinary write rejection without using an exception as control flow', () => {
    const target = { first: 0, second: 0 }
    const current = new Proxy(target, {
      defineProperty: () => false,
      set(object, key, value) {
        return key !== 'second' && Reflect.set(object, key, value)
      },
    })
    const root = capture(builtinTypes, { first: 1, second: 2 }).nodes[0]
    expect(
      builtinTypes.policies[root.layout.kind].publish(root, current, (edge) =>
        isNode(edge) ? undefined : atomValue(edge),
      ),
    ).toBe(false)
    expect(target).toEqual({ first: 1, second: 0 })
  })
})
