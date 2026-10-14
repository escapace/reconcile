import { builtinTypes } from '../types/builtins'
import { assert, describe, expect, it } from 'vitest'
import { capture } from '../publication/capture'
import { candidates } from '../publication/candidates'
import { selections } from '../graph/selection'

function problem(current: object, next: object) {
  const records = capture(builtinTypes, next).nodes
  return { domains: candidates(builtinTypes, records, current), records }
}

describe('native candidate constraint compiler', () => {
  it('compiles fixed cycles and shared references without making a selection or writing input', () => {
    const child = { n: 0 }
    const current = { child, self: {} }
    current.self = current
    Object.freeze(current)
    const next = { child: { n: 1 }, self: {} }
    next.self = next
    const { domains } = problem(current, next)
    const plans = [...selections(domains)]
    expect(plans).toHaveLength(1)
    expect(plans[0].map((choice, node) => domains[node][choice].identity)).toEqual([current, child])
    expect(child.n).toBe(0)
  })

  it('rejects incompatible fixed identities, storage and own surfaces before publication', () => {
    const shared = { n: 1 }
    const cases: Array<[object, object]> = [
      [Object.freeze({ left: {}, right: {} }), { left: shared, right: shared }],
      [Object.freeze({ left: shared, right: shared }), { left: {}, right: {} }],
      [Object.preventExtensions({ n: 0 }), { added: 2, n: 1 }],
      [Object.freeze({ n: 0 }), { n: 1 }],
      [new ArrayBuffer(1), new ArrayBuffer(2)],
    ]
    for (const [current, next] of cases)
      expect([...selections(problem(current, next).domains)]).toEqual([])
  })

  it('scores view retention and buffer ownership through one conditional rule', () => {
    const first = new ArrayBuffer(4)
    const second = new ArrayBuffer(4)
    const view = new Uint8Array(second)
    const nextBuffer = new ArrayBuffer(4)
    const { domains } = problem(
      { a: first, b: second, view },
      { a: nextBuffer, b: nextBuffer, view: new Uint8Array(nextBuffer) },
    )
    const selected = selections(domains).next().value
    assert(selected !== undefined)
    expect(domains[1][selected[1]].identity).toBe(second)
    expect(domains[2][selected[2]].identity).toBe(view)
  })

  it('preserves compatible children when a fixed parent candidate cannot be retained', () => {
    const child = { n: 0 }
    const parent = Object.freeze({ child, obsolete: 1 })
    const { domains } = problem({ parent }, { parent: { child: { n: 2 } } })
    const selected = selections(domains).next().value
    assert(selected !== undefined)
    expect(domains[1][selected[1]].retained).toBe(false)
    expect(domains[2][selected[2]].identity).toBe(child)
    expect(child.n).toBe(0)
  })
  it('observes only object-aligned Map tuple slots during candidate discovery', () => {
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
    expect(events).toEqual(['value'])
    const selected = selections(domains).next().value
    assert(selected !== undefined)
    expect(domains[1][selected[1]].identity).toBe(child)
  })
  it('does not coerce collection sizes into a successful native readback', () => {
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
          (actual, edge) => 'value' in edge && Object.is(actual, edge.value),
        ),
      ).toBe(false)
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
        'value' in edge ? edge.value : undefined,
      ),
    ).toBe(false)
    expect(target).toEqual({ first: 1, second: 0 })
  })
})
