import { expect, it } from 'vitest'
import { runDriver } from './fixtures/run-driver'

// Properties added to Object.prototype or Array.prototype change no internal read, write,
// descriptor or iterator close, and objects the library builds hold their own data whatever
// Object.prototype holds.
it('keeps every operation independent of added standard-prototype properties', async () => {
  const output = await runDriver('standard-prototypes.ts', [])
  expect(output.cases).toBeGreaterThan(100)
  expect(output.failures).toEqual([])
})

// Under frozen intrinsics a recipe's assignment behaves as plain assignment, and every new object
// holds the keys standard prototypes hold as accessors.
it('behaves as plain assignment under node --frozen-intrinsics', async () => {
  const output = await runDriver('frozen-intrinsics.ts', ['--frozen-intrinsics'])
  expect(output.cases).toBe(7)
  expect(output.failures).toEqual([])
})

// Every function on every value kind behaves the same when standard methods are accessors, as
// `node --frozen-intrinsics` makes them, as in an ordinary runtime.
it('behaves the same for every value kind under node --frozen-intrinsics', async () => {
  const plain = await runDriver('hardened-kinds.ts', [])
  const frozen = await runDriver('hardened-kinds.ts', ['--frozen-intrinsics'])
  expect(plain.failures).toEqual([])
  expect(plain.cases).toBeGreaterThan(120)
  expect(plain.frozen).toBe(false)
  expect(frozen.frozen).toBe(true)
  expect(frozen.outcomes).toEqual(plain.outcomes)
})

// SES `lockdown` freezes every intrinsic and, with severe override taming, turns the methods of
// standard prototypes into accessors. Every function on every value kind behaves as in an ordinary
// runtime, whether the library is imported before or after `lockdown`.
it('behaves the same for every value kind under SES, imported before or after lockdown', async () => {
  const plain = await runDriver('hardened-kinds.ts', [])
  for (const order of ['before', 'after'] as const)
    for (const taming of ['default', 'severe'] as const) {
      const locked = await runDriver('hardened-kinds.ts', [], { order, taming })
      expect(locked.frozen).toBe(true)
      expect(locked.outcomes, `${order} lockdown, ${taming} taming`).toEqual(plain.outcomes)
    }
})

// The documented contracts of public-api-invariants.spec.ts hold on a sample of random graphs under
// `node --frozen-intrinsics` and under SES `lockdown` with severe override taming.
it('keeps the documented contracts under node --frozen-intrinsics', async () => {
  const output = await runDriver('invariants-hardened.ts', ['--frozen-intrinsics'])
  expect(output.cases).toBeGreaterThan(100)
  expect(output.failures).toEqual([])
})

it('keeps the documented contracts under SES lockdown with severe override taming', async () => {
  const output = await runDriver('invariants-hardened.ts', [], { order: 'after', taming: 'severe' })
  expect(output.frozen).toBe(true)
  expect(output.cases).toBeGreaterThan(100)
  expect(output.failures).toEqual([])
})
