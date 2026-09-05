import { assert, describe, it } from 'vitest'
import { createPatch } from '../index'

describe('unread specials in replacement graphs', () => {
  const containers = [
    {
      name: 'object',
      read: (container: unknown) => (container as { value: object }).value,
      wrap: (value: object) => ({ value }),
    },
    {
      name: 'array',
      read: (container: unknown) => (container as object[])[0],
      wrap: (value: object) => [value],
    },
    {
      name: 'map',
      read: (container: unknown) => (container as Map<string, object>).get('value'),
      wrap: (value: object) => new Map([['value', value]]),
    },
    {
      name: 'set',
      read: (container: unknown) => [...(container as Set<object>)][0],
      wrap: (value: object) => new Set([value]),
    },
  ]
  for (const value of [
    new Date(1),
    new ArrayBuffer(2),
    new DataView(new ArrayBuffer(2)),
    new Uint8Array(2),
  ]) {
    for (const container of containers) {
      for (const reverse of [false, true]) {
        it(`preserves ${Object.prototype.toString.call(value)} sharing through ${container.name} (reverse: ${reverse})`, () => {
          const current = { child: { count: 0 } }
          const nested = container.wrap(value)
          const result = createPatch(current, (draft) => {
            draft.child.count = 1
            return reverse
              ? { child: draft.child, direct: value, nested }
              : { ...{ nested }, child: draft.child, direct: value }
          })
          assert.equal(result.direct, container.read(result.nested))
          assert.notEqual(result.direct, value)
          assert.equal(result.child.count, 1)
          assert.equal(current.child.count, 0)
        })
      }
    }
  }

  for (const changed of [false, true]) {
    it(`preserves buffers shared by replacement and unread views (changed: ${changed})`, () => {
      const buffer = new ArrayBuffer(4)
      const current = { writer: new Uint8Array(buffer) }
      const view = new DataView(buffer, 1, 2)
      const result = createPatch(current, (draft) => {
        if (changed) draft.writer[1] = 9
        return { buffer, nested: { view }, view, writer: draft.writer }
      })
      assert.equal(result.view, result.nested.view)
      assert.equal(result.buffer, result.writer.buffer)
      assert.equal(result.view.buffer, result.buffer)
      assert.equal(result.view.getUint8(0), changed ? 9 : 0)
      assert.equal(new Uint8Array(buffer)[1], 0)
    })
  }

  it('propagates clone requirements through previously reused subtrees', () => {
    const first = new Date(1)
    const second = new Date(2)
    const third = new Date(3)
    const current = { child: {} }
    const result = createPatch(current, (draft) => ({
      a: { next: third, value: second },
      b: { next: second, value: first },
      child: draft.child,
      direct: first,
    }))
    assert.equal(result.direct, result.b.value)
    assert.equal(result.b.next, result.a.value)
    assert.notEqual(result.direct, first)
    assert.notEqual(result.a.value, second)
    assert.notEqual(result.a.next, third)
  })

  it('preserves aliases into a reused cyclic draft subtree', () => {
    const date = new Date(1)
    const branch: { date: Date; self?: object } = { date }
    branch.self = branch
    const current = { branch }
    const result = createPatch(current, (draft) => ({
      branch: draft.branch,
      direct: date,
    }))
    assert.equal(result.direct, result.branch.date)
    assert.equal(result.branch.self, result.branch)
    assert.equal(current.branch.self, current.branch)
    assert.equal(current.branch.date, date)
  })
})
