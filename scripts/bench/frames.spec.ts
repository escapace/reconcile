import { expect, it } from 'vitest'
import { attribute, type AttributionFrame } from './frames'

const caller: AttributionFrame = {
  functionName: 'caller',
  location: 'src/core.ts:1:1',
  scope: 'project',
}
const leaf: AttributionFrame = {
  functionName: 'leaf',
  location: 'src/type.ts:1:1',
  scope: 'project',
}
const native: AttributionFrame = { functionName: 'native', location: 'native', scope: 'unmapped' }
const external: AttributionFrame = {
  functionName: 'dependency',
  location: 'node_modules/pkg.js',
  scope: 'mapped',
}

it('attributes external and native work to project callers without losing coverage', () => {
  const result = attribute([
    { frame: caller, id: 1, weight: 2 },
    { frame: leaf, id: 2, parent: 1, weight: 3 },
    { frame: native, id: 3, parent: 2, weight: 5 },
    { frame: external, id: 4, parent: 1, weight: 7 },
  ])
  expect(result.coverage).toEqual({ mapped: 7, project: 5, total: 17, unmapped: 5 })
  expect(result.frames.find((frame) => frame.functionName === 'caller')).toMatchObject({
    inclusive: 17,
    self: 2,
  })
  expect(result.frames.find((frame) => frame.functionName === 'leaf')).toMatchObject({
    inclusive: 8,
    self: 3,
  })
})

it('counts recursion once per sample for inclusive source attribution', () => {
  const result = attribute([
    { frame: caller, id: 1, weight: 2 },
    { frame: caller, id: 2, parent: 1, weight: 3 },
    { frame: leaf, id: 3, parent: 2, weight: 5 },
  ])
  expect(result.frames.find((frame) => frame.functionName === 'caller')).toMatchObject({
    inclusive: 10,
    self: 5,
  })
})

it('rejects malformed profile ancestry rather than silently dropping samples', () => {
  expect(() => attribute([{ frame: caller, id: 1, parent: 1, weight: 1 }])).toThrow('Cyclic')
  expect(() => attribute([{ frame: caller, id: 1, parent: 2, weight: 1 }])).toThrow('Missing')
})

it('retains unparsed bailout events and separates warmup from measured deoptimizations', async () => {
  const { parseDeopts } = await import('./frames')
  const event =
    '[bailout (kind: deopt-eager, reason: wrong map): begin. deoptimizing 0x0 <JSFunction work (sfi = 0x1)>]'
  const result = parseDeopts(
    `RECONCILE_PHASE warmup\n${event}\nRECONCILE_PHASE measurement\n${event}\n${event}\n[bailout unknown format]\n`,
  )
  expect(result.coverage).toEqual({ parsed: 3, total: 4, unparsed: 1 })
  expect(result.entries).toContainEqual({
    count: 2,
    functionName: 'work',
    parsed: true,
    phase: 'measurement',
    reason: 'wrong map',
  })
  expect(result.entries).toContainEqual({
    count: 1,
    functionName: 'work',
    parsed: true,
    phase: 'warmup',
    reason: 'wrong map',
  })
})
