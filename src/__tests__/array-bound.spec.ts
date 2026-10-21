import assert from 'node:assert/strict'
import { it } from 'vitest'
import { DraftSession } from '../draft-session'
import { produce } from '../index'
import { builtinTypes } from '../types/builtins'
import type { PropertyDraftState } from '../types/shared/draft-properties'

it('preserves native array histories through holes, insertion, deletion and repeated shrinking', () => {
  for (const size of [0, 1, 4, 16, 128]) {
    const source = Array.from({ length: size }, (_, index) => index)
    for (let index = 1; index < size; index += 3) Reflect.deleteProperty(source, index)
    const expected = source.slice()
    const operations = (array: number[]) => {
      const trace: unknown[] = []
      array.length += 3
      array[array.length - 2] = 42
      Reflect.deleteProperty(array, array.length - 2)
      if (size > 0) {
        Reflect.deleteProperty(array, size - 1)
        array[size - 1] = 99
      }
      while (array.length > 0) {
        trace.push(array.pop())
        if (array.length % 4 === 0) array.length = Math.max(0, array.length - 1)
      }
      array.push(8, 9)
      trace.push(array.pop())
      return trace
    }
    const expectedTrace = operations(expected)
    const before = source.slice()
    const result = produce(source, (draft) => {
      assert.deepEqual(operations(draft), expectedTrace)
      return draft
    })
    assert.deepEqual(result, expected)
    assert.deepEqual(source, before)
  }
})

it('applies both coercion effects before deciding whether a shrink has keys to delete', () => {
  for (const action of ['insert', 'delete', 'shrink', 'grow'] as const) {
    const traces: unknown[][] = []
    const recipe = (array: number[]) => {
      array.pop()
      const trace: unknown[] = []
      const accepted = Reflect.set(array, 'length', {
        valueOf() {
          trace.push(array.length)
          if (action === 'insert') array[7] = 7
          if (action === 'delete') Reflect.deleteProperty(array, 1)
          if (action === 'shrink') array.length = 1
          if (action === 'grow') array.length = 9
          return 2
        },
      })
      traces.push([accepted, ...trace])
      return array
    }
    const expected = recipe([0, 1, 2])
    const source = [0, 1, 2]
    assert.deepEqual(produce(source, recipe), expected)
    assert.deepEqual(traces[0], traces[1])
    assert.deepEqual(source, [0, 1, 2])
  }
})

it('rebinds an array summary after a first-copy read installs a temporary private store', () => {
  const cell: { handle?: number[] } = {}
  let entered = false
  const source = new Proxy([0, 1, 2, 3], {
    get(target, key, receiver) {
      if (key === '0' && cell.handle !== undefined && !entered) {
        entered = true
        cell.handle.length = 0
      }
      return Reflect.get(target, key, receiver) as unknown
    },
  })
  const session = new DraftSession(builtinTypes)
  const handle = session.createDraft(source)
  cell.handle = handle
  handle.pop()
  assert.equal(entered, true)
  handle.length = 1
  assert.deepEqual(Reflect.ownKeys(handle), ['0', 'length'])
  assert.equal(handle[0], 0)
  assert.deepEqual(source, [0, 1, 2, 3])
})

it('does not account an absent deletion against a store installed by its descriptor trap', () => {
  const cell: { handle?: number[] } = {}
  let entered = false
  const source = new Proxy([0, 1], {
    getOwnPropertyDescriptor(target, key) {
      if (key === '3' && cell.handle !== undefined && !entered) {
        entered = true
        cell.handle[3] = 3
      }
      return Reflect.getOwnPropertyDescriptor(target, key)
    },
  })
  const session = new DraftSession(builtinTypes)
  const handle = session.createDraft(source)
  cell.handle = handle
  assert.equal(Reflect.deleteProperty(handle, '3'), true)
  assert.equal(handle[3], 3)
  handle.length = 3
  assert.equal(3 in handle, false)
  assert.equal(handle.length, 3)
})

it('retains partial failure and numeric-key boundaries after summary updates', () => {
  const session = new DraftSession(builtinTypes)
  const handle = session.createDraft([0, 1, 2, 3])
  const state = session.statesByIdentity.get(handle) as PropertyDraftState
  handle.pop()
  state.copy!['1'].configurable = false
  assert.equal(Reflect.set(handle, 'length', 0), false)
  assert.equal(handle.length, 2)
  assert.equal(2 in handle, false)
  assert.equal(state.modified, true)
  const symbol = Symbol('marker')
  // Keys an array result cannot carry are refused, as by a non-extensible object.
  for (const key of ['01', '4294967295', symbol]) assert.equal(Reflect.set(handle, key, 42), false)
  Reflect.set(handle, '4294967294', 9)
  assert.equal(handle.length, 4_294_967_295)
  assert.equal(Reflect.deleteProperty(handle, '4294967294'), true)
  assert.equal(Reflect.set(handle, 'length', 2), true)
  for (const key of ['01', '4294967295', symbol]) assert.equal(Reflect.get(handle, key), undefined)
  state.copy!.length.writable = false
  assert.equal(Reflect.set(handle, 'length', 1), false)
  assert.equal(Reflect.set(handle, '2', 7), false)
})

it('keeps summary updates on held handles isolated after publication', () => {
  let held: number[] | undefined
  const source = [0, 1, 2]
  const result = produce(source, (draft) => {
    held = draft
    draft.pop()
    return draft
  })
  held!.push(3)
  held!.pop()
  held!.length = 0
  held!.push(4)
  held!.pop()
  assert.deepEqual(result, [0, 1])
  assert.deepEqual(source, [0, 1, 2])
  assert.equal(held!.length, 0)
})
