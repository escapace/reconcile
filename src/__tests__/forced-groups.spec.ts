import { assert, it } from 'vitest'
import { produce, reconcile } from '../index'
import { ring, type RingNode } from './fixtures/ring'

it.each([2, 4, 8])(
  'preserves distinct desired cycles competing for one frozen ring of size %s',
  (size) => {
    const original = ring(size)
    original.forEach((node) => {
      Object.freeze(node.payload)
      Object.freeze(node)
    })
    const left = ring(size)
    const right = ring(size)
    const holder = { left: original[0], right: original[0] }
    const result = reconcile(holder, { left: left[0], right: right[0] })
    assert.equal(result, holder)
    const collected: RingNode[][] = []
    for (const root of [result.left, result.right]) {
      const nodes: RingNode[] = []
      let cursor = root
      for (let index = 0; index < size; index += 1) {
        assert.equal(cursor.payload.value, 0)
        nodes.push(cursor)
        cursor = cursor.next!
      }
      assert.equal(cursor, root)
      collected.push(nodes)
    }
    assert.isTrue(collected[0].every((node) => !collected[1].includes(node)))
    assert.equal(collected.flat().filter((node) => original.includes(node)).length, size)
    assert.isTrue(original.every((node, index) => node.next === original[(index + 1) % size]))
  },
)

it.each([2, 4, 8])(
  'replaces the changed frozen cycle and preserves immutable produce inputs of size %s',
  (size) => {
    const original = ring(size)
    const desired = ring(size)
    original.forEach((node) => {
      Object.freeze(node.payload)
      Object.freeze(node)
    })
    desired[size - 1].payload.value = 1
    const holder = { start: original[0] }
    const output = reconcile(holder, { start: desired[0] })
    assert.equal(output, holder)
    let cursor = output.start
    for (let index = 0; index < size; index += 1) {
      assert.equal(cursor.payload.value, index === size - 1 ? 1 : 0)
      cursor = cursor.next!
    }
    assert.equal(cursor, output.start)
    assert.isTrue(original.every((node) => node.payload.value === 0))

    const input = ring(size)
    input.forEach(Object.freeze)
    const patched = produce(input[0], (draft) => {
      let node = draft
      for (let index = 1; index < size; index += 1) node = node.next!
      node.payload.value = 1
      return draft
    })
    cursor = patched
    for (let index = 0; index < size; index += 1) {
      assert.equal(cursor.payload.value, index === size - 1 ? 1 : 0)
      cursor = cursor.next!
    }
    assert.equal(cursor, patched)
    assert.isTrue(input.every((node) => node.payload.value === 0))
  },
)
