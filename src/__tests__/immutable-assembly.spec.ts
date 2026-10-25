import { expect, it } from 'vitest'
import { compileImmutable } from '../restore-identities'
import { OBJECT_KIND } from '../types/object'
import { produceTypes } from '../types/builtins'
import type { ImmutableRegistry, ReuseNode } from '../types'

it('preserves reservation and completion reads through child-first cyclic reuse', () => {
  const trace: string[] = []
  const initialParent = {}
  const completedParent = {}
  const childTarget = {}
  let parentReads = 0
  const parent: ReuseNode = {
    children: [],
    discoveredBy: undefined,
    layout: { kind: OBJECT_KIND },
    get settled() {
      trace.push('parent.settled')
      return false
    },
    get target() {
      parentReads += 1
      trace.push(`parent.target:${parentReads}`)
      return parentReads === 1 ? initialParent : completedParent
    },
  }
  const child: ReuseNode = {
    children: [parent],
    discoveredBy: undefined,
    layout: { kind: OBJECT_KIND },
    get settled() {
      trace.push('child.settled')
      return false
    },
    get target() {
      trace.push('child.target')
      return childTarget
    },
  }
  parent.children.push(child)
  const types: ImmutableRegistry = {
    ...produceTypes,
    structural: {
      ...produceTypes.structural,
      [OBJECT_KIND]: {
        ...produceTypes.structural[OBJECT_KIND],
        reuse(payload, target, compare) {
          const isChild = target === childTarget
          trace.push(isChild ? 'child.reuse' : 'parent.reuse')
          expect(compare(isChild ? initialParent : childTarget, payload.edges[0])).toBe(true)
          return true
        },
      },
    },
  }
  const result = compileImmutable(types, parent)
  expect(result.records[0].target).toBe(completedParent)
  expect(result.records[1].target).toBe(childTarget)
  expect(result.unavailable.size).toBe(0)
  expect(trace).toEqual([
    'parent.target:1',
    'child.target',
    'child.settled',
    'child.target',
    'child.settled',
    'child.target',
    'child.reuse',
    'parent.settled',
    'parent.target:2',
    'parent.settled',
    'parent.target:3',
    'parent.reuse',
  ])
})
