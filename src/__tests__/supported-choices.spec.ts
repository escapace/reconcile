import { assert, it } from 'vitest'
import { unsupportedChoices } from '../graph/supported-choices'
import { selections } from '../graph/selection'
import { reconcile } from '../index'
import type { Choice, Domains } from '../types'
import { ring } from './fixtures/ring'

const choice = (identity: number, required: Choice['required'] = [], retained = true): Choice => ({
  identity,
  required,
  retained,
  storage: identity,
})
const mask = (domains: Domains) => unsupportedChoices(domains)?.map((row) => Array.from(row))

it('certifies supported cycles and duplicate live alternatives without deleting them', () => {
  assert.isUndefined(
    mask([
      [choice(0, [{ identity: 1, node: 1 }])],
      [choice(1, [{ identity: 0, node: 0 }]), choice(1)],
    ]),
  )
})

it('propagates last-support loss but not the loss of one equal-identity alternative', () => {
  const domains = [
    [choice(0, [{ identity: 1, node: 1 }])],
    [choice(1, [{ identity: 3, node: 3 }]), choice(1)],
  ]
  assert.deepEqual(mask(domains), [[0], [1, 0]])
  assert.deepEqual(mask([domains[0], [domains[1][0], domains[1][0]]]), [[1], [1, 1]])
})

it('checks self requirements against this choice, and admits duplicate demands only once', () => {
  assert.deepEqual(mask([[choice(0, [{ identity: 1, node: 0 }]), choice(1)]]), [[1, 0]])
  assert.deepEqual(
    mask([
      [
        choice(0, [
          { identity: 1, node: 1 },
          { identity: 1, node: 1 },
        ]),
      ],
      [choice(1, [{ identity: 2, node: 2 }])],
    ]),
    [[1], [1]],
  )
  assert.isUndefined(mask([]))
  assert.isUndefined(mask([[]]))
})

it('keeps callback tiers and original choice indices after support deletion', () => {
  const domains = [
    [choice(0, [{ identity: 1, node: 1 }]), choice(2, [], false)],
    [choice(1, [{ identity: 8, node: 2 }]), choice(3, [], false)],
  ]
  const tiers: number[] = []
  assert.deepEqual(
    [
      ...selections(domains, (score) => {
        tiers.push(score)
        return new Set([0, 1])
      }),
    ],
    [[1, 1]],
  )
  assert.deepEqual(tiers, [2, 1, 0])
  tiers.length = 0
  assert.deepEqual(
    [
      ...selections([[domains[0][0]], [domains[1][0]]], (score) => {
        tiers.push(score)
        return new Set()
      }),
    ],
    [],
  )
  assert.deepEqual(tiers, [2])
})

it('handles deep cascades iteratively and leaves supplied domains unchanged', () => {
  const domains = Array.from({ length: 12_000 }, (_, node) =>
    Object.freeze([Object.freeze(choice(node, [{ identity: node + 1, node: node + 1 }]))]),
  )
  Object.freeze(domains)
  assert.isTrue(unsupportedChoices(domains)!.every((row) => row[0] === 1))
})

it('replaces a changed frozen size-16 ring through its mutable holder', () => {
  const original = ring(16)
  const desired = ring(16)
  original.forEach((node) => {
    Object.freeze(node.payload)
    Object.freeze(node)
  })
  desired[15].payload.value = 1
  const holder = { start: original[0] }
  const result = reconcile(holder, { start: desired[0] })
  assert.equal(result, holder)
  let cursor = result.start
  for (let index = 0; index < 16; index += 1) {
    assert.notEqual(cursor, original[index])
    assert.equal(cursor.payload.value, index === 15 ? 1 : 0)
    assert.equal(original[index].payload.value, 0)
    cursor = cursor.next!
  }
  assert.equal(cursor, result.start)
})
