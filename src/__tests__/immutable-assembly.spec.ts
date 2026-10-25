import { expect, it } from 'vitest'
import { compileImmutable } from '../restore-identities'
import { createEngine } from '../engine'
import { Cell, cellType } from './fixtures/cell-type'
import type { ImmutableRegistry, ReuseNode } from '../types'

it('preserves reservation and completion reads through child-first cyclic reuse', () => {
  const trace: string[] = []
  const initialParent = new Cell(undefined)
  const completedParent = new Cell(undefined)
  const childTarget = new Cell(undefined)
  let parentReads = 0
  const parent: ReuseNode = {
    children: [],
    discoveredBy: undefined,
    layout: { kind: cellType.kind },
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
    layout: { kind: cellType.kind },
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
  const registry = createEngine({ types: [cellType] }).types
  const types: ImmutableRegistry = {
    ...registry,
    structural: {
      ...registry.structural,
      [cellType.kind]: {
        ...registry.structural[cellType.kind],
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
