import { scope, type } from 'arktype'
import { describe, expect, it } from 'vitest'
import { deserialize, serialize } from '../index'

// The README's untrusted-input contract, pinned for ArkType, the canonical Standard Schema
// validator: it checks each shared object once, accepts cycles in bounded time, and checks
// array length bounds before it iterates.
const roundTrip = (value: unknown) =>
  deserialize(JSON.parse(JSON.stringify(serialize(value))), { maxBytes: 1_000_000 })

const { node } = scope({ node: { 'left?': 'node', 'right?': 'node', 'value': 'number' } }).export()

// Each level references the level below twice: 41 objects, about 2^40 paths as a tree.
function doublingChain(leaf: unknown): unknown {
  let level: Record<string, unknown> = { value: leaf }
  for (let depth = 0; depth < 40; depth++) level = { left: level, right: level, value: depth }
  return level
}

// Standard Schema allows an asynchronous result; ArkType validates synchronously.
function validate(
  schema: { '~standard': { validate: (value: unknown) => unknown } },
  value: unknown,
): unknown {
  const result = schema['~standard'].validate(value)
  expect(result).not.toBeInstanceOf(Promise)
  return result
}

function timed<T>(run: () => T): { elapsed: number; result: T } {
  const start = performance.now()
  const result = run()
  return { elapsed: performance.now() - start, result }
}

describe('ArkType on deserialized graphs', () => {
  it('validates a cycle through a recursive type', () => {
    const value: Record<string, unknown> = { value: 1 }
    value.left = value
    const decoded = roundTrip(value) as Record<string, unknown>
    expect(decoded.left).toBe(decoded)
    expect(validate(node, decoded)).toEqual({ value: decoded })
  })

  // Walking either value as a tree would take about 2^40 steps; the bounds leave room for a slow
  // machine and the validator's first-call compilation.
  it('validates each shared object once, valid or not', () => {
    const validChain = roundTrip(doublingChain(0))
    const invalidChain = roundTrip(doublingChain('zero'))
    const valid = timed(() => validate(node, validChain))
    expect(valid.result).not.toHaveProperty('issues')
    expect(valid.elapsed).toBeLessThan(2000)
    const invalid = timed(() => validate(node, invalidChain))
    expect(invalid.result).toHaveProperty('issues')
    expect(invalid.elapsed).toBeLessThan(2000)
  })

  it('checks an array length bound before iterating a sparse array', () => {
    const decoded = deserialize([[0, 0, 1, 3], [[4_294_967_295, [0], []]]], { maxBytes: Infinity })
    const bounded = type('string[] <= 100')
    // Iterating 4,294,967,295 entries would take minutes.
    const { elapsed, result } = timed(() => validate(bounded, decoded))
    expect(result).toHaveProperty('issues')
    expect(elapsed).toBeLessThan(2000)
  })

  it('runs the README example', () => {
    const Message = type({ '+': 'delete', 'id': 'number', 'tags': 'string[] <= 16' })
    const body = JSON.stringify(serialize({ id: 1, tags: ['a', 'b'] }))
    const result = Message(deserialize(JSON.parse(body), { maxBytes: 64_000 }))
    expect(result instanceof type.errors).toBe(false)
    // Undeclared keys are deleted, so a cycle hidden under one does not reach the application.
    const extra: Record<string, unknown> = { id: 1, tags: [] }
    extra.extra = extra
    const pruned = Message(
      deserialize(JSON.parse(JSON.stringify(serialize(extra))), { maxBytes: 64_000 }),
    )
    expect(JSON.stringify(pruned)).toBe('{"id":1,"tags":[]}')
    const tooMany = JSON.stringify(serialize({ id: 1, tags: Array.from({ length: 17 }, String) }))
    expect(
      Message(deserialize(JSON.parse(tooMany), { maxBytes: 64_000 })) instanceof type.errors,
    ).toBe(true)
  })
})
