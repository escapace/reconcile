import { OBJECT_KIND } from '../types/object'
import { produceTypes } from '../types/builtins'
import type { ObjectLayout } from '../types/object'
import { describe, expect, it } from 'vitest'
import { compileImmutable, restoreIdentities } from '../restore-identities'
import { immutableDomains, rankedSelections } from './fixtures/compact-immutable'
import type { ImmutableRegistry, ReuseNode } from '../types'

function record(target: Record<string, unknown>, n: number): ReuseNode<ObjectLayout> {
  return {
    attributes: Object.keys(target).map(() => 7),
    children: Object.entries(target).map(([key, value]) =>
      key === 'n' ? n : { target: value as object },
    ),
    discoveredBy: undefined,
    keys: Object.keys(target),
    layout: { hidden: undefined, kind: OBJECT_KIND, prototype: Object.prototype, slots: undefined },
    target,
  }
}

describe('complete immutable graph compilation', () => {
  it('includes fixed specials, aliases and backing-buffer edges without reading scalar payloads', () => {
    class UnobservedDate extends Date {
      override getTime(): number {
        throw new Error('Settled scalar must not be observed again')
      }
    }
    const date = new UnobservedDate(7)
    const buffer = new ArrayBuffer(8)
    const typed = new Uint8Array(buffer, 2, 3)
    const view = new DataView(buffer, 1, 5)
    const current = { buffer, date, n: 0, repeated: date, typed, view }
    const source = record(current, 1)
    const problem = compileImmutable(produceTypes, source)
    const { records, root } = problem
    const domains = immutableDomains(problem)
    expect(records).toHaveLength(5)
    expect(root).toBe(4)
    const bufferNode = records.findIndex((node) => node.target === buffer)
    const rootEdges = records[root].edges
    expect(rootEdges[1]).toBe(rootEdges[3])
    for (const value of [typed, view]) {
      const node = records.findIndex((entry) => entry.target === value)
      expect(records[node].edges).toEqual([{ node: bufferNode }])
      expect(records[node].edges[0]).toBe(rootEdges[0])
      expect(domains[node]).toHaveLength(1)
      expect(domains[node][0].required).toEqual([
        { identity: domains[bufferNode][0].identity, node: bufferNode },
      ])
    }
    const plans = rankedSelections(domains)
    expect(plans).toHaveLength(1)
    const result = restoreIdentities(produceTypes, source, true)!
    for (const key of ['buffer', 'date', 'repeated', 'typed', 'view'] as const)
      expect(Reflect.get(result, key)).toBe(current[key])
    expect(Reflect.get(result, 'n')).toBe(1)
    expect(result).not.toBe(current)
    expect(current.n).toBe(0)
  })

  it('retains unchanged structural parents of fixed specials', () => {
    const current = { date: new Date(7), n: 0 }
    expect(restoreIdentities(produceTypes, record(current, 0), true)).toBe(current)
  })

  it('propagates a late cyclic failure through locally passing parents and duplicate aliases', () => {
    const current: { n: number; next?: object } = { n: 0 }
    const child = { left: current, right: current }
    current.next = child
    const source = record(current, 1)
    const nextChild = record(child, 0)
    source.children[1] = nextChild
    nextChild.children.splice(0, 2, source, source)
    const checks: object[] = []
    const policy = produceTypes.structural[OBJECT_KIND]
    const types: ImmutableRegistry = {
      ...produceTypes,
      structural: {
        ...produceTypes.structural,
        [OBJECT_KIND]: {
          ...policy,
          reuse(payload, target, resolve) {
            checks.push(target)
            return policy.reuse(payload, target, resolve)
          },
        },
      },
    }
    const problem = compileImmutable(types, source)
    const { records, root } = problem
    const domains = immutableDomains(problem)
    expect(checks).toEqual([child, current])
    expect(root).toBe(0)
    expect(records[1].edges).toEqual([{ node: 0 }, { node: 0 }])
    expect(records[1].edges[0]).toBe(records[1].edges[1])
    expect(domains.map((domain) => domain.map((choice) => choice.retained))).toEqual([
      [false],
      [false],
    ])
    expect(rankedSelections(domains)).toEqual([[0, 0]])
    const result = restoreIdentities(types, source, true) as typeof current
    expect(result).not.toBe(current)
    expect(result.n).toBe(1)
    expect(result.next).not.toBe(child)
    expect(Reflect.get(result.next!, 'left')).toBe(result)
    expect(Reflect.get(result.next!, 'right')).toBe(result)
    expect(current.n).toBe(0)
  })

  it('continues after a failed eligibility mask without building that mask again', () => {
    const child = { n: 0 }
    const current = { child, n: 0 }
    const source = record(current, 1)
    source.children[0] = record(child, 0)
    const allocated: object[] = []
    let fills = 0
    const structural = produceTypes.structural[OBJECT_KIND]
    const types: ImmutableRegistry = {
      ...produceTypes,
      structural: {
        ...produceTypes.structural,
        [OBJECT_KIND]: {
          ...structural,
          allocate(node) {
            allocated.push(node)
            return structural.allocate(node)
          },
          // The first copy cannot hold its slots, as a collapsing Map could not, so the
          // eligibility mask (child kept) is rejected.
          fill: (node, target, resolve) => ++fills !== 1 && structural.fill(node, target, resolve),
        },
      },
    }
    const result = restoreIdentities(types, source, true) as typeof current
    // The stream's next mask copies both records; the rejected mask is not attempted again.
    expect(allocated).toHaveLength(3)
    expect(result.child).not.toBe(child)
    expect(result.child).toEqual({ n: 0 })
    expect(result.n).toBe(1)
    expect(current.child).toBe(child)
  })

  it('interns structural aliases and cycles before collecting their children', () => {
    const child = { n: 0 }
    const current: { left: typeof child; right: typeof child; self?: object } = {
      left: child,
      right: child,
    }
    current.self = current
    const source = record(current, 0)
    const nextChild = record(child, 1)
    source.children.splice(0, source.children.length, nextChild, nextChild, source)
    const { records, root } = compileImmutable(produceTypes, source)
    expect(records).toHaveLength(2)
    expect(records[root].edges[0]).toBe(records[root].edges[1])
    expect(records[root].edges[2]).toEqual({ node: root })
    const result = restoreIdentities(produceTypes, source, true) as typeof current
    expect(result.self).toBe(result)
    expect(result.left).toBe(result.right)
    expect(result.left).toEqual({ n: 1 })
    expect(result.left).not.toBe(child)
    expect(current.left.n).toBe(0)
    expect(current.self).toBe(current)
  })
})
