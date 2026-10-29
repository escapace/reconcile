import { readdirSync } from 'node:fs'
import { describe, expect, it } from 'vitest'
import { BRIDGES } from '.'
import { parseSeeds, reproduce, selectBatches } from './selection'
import { phaseBatchNames } from './spec-phases'
import { specBatchNames } from './spec'
import { universeNames } from './spec-enumeration'

const batchesOf = (family: string): readonly string[] | undefined =>
  BRIDGES.find((bridge) => bridge.family === family)?.batches

describe('the bridge registry', () => {
  it('names every bridge file once, by its file name', () => {
    const files = readdirSync(import.meta.dirname)
      .filter((file) => file.endsWith('.ts') && !file.endsWith('.spec.ts'))
      .map((file) => file.slice(0, -'.ts'.length))
      .filter((name) => name !== 'index' && name !== 'selection')
    const families = BRIDGES.map((bridge) => bridge.family)
    expect(new Set(families).size).toBe(families.length)
    expect([...families].sort()).toEqual(files.sort())
  })

  it('lists the batches each bridge runs, in its order', () => {
    expect(batchesOf('spec')).toEqual(specBatchNames())
    expect(batchesOf('spec-phases')).toEqual(phaseBatchNames())
    expect(batchesOf('spec-enumeration')).toEqual(universeNames())
    expect(BRIDGES.filter((bridge) => bridge.batches !== undefined)).toHaveLength(3)
  })
})

describe('a selection', () => {
  it('reads seeds and ranges, once each, and refuses anything else', () => {
    expect(parseSeeds('3-5,1, 4,10563')).toEqual([3, 4, 5, 1, 10_563])
    for (const text of ['0', '5-2', 'x', '', '1,,2', '-3'])
      expect(() => parseSeeds(text)).toThrow('--seeds takes seeds and ranges')
  })

  it('selects the batch it names, or every batch, and prints the command for one seed', () => {
    const batches = [{ name: 'plain' }, { name: 'hazards' }]
    expect(selectBatches(batches, {})).toEqual(batches)
    expect(selectBatches(batches, { batch: 'hazards' })).toEqual([{ name: 'hazards' }])
    expect(reproduce('spec', 'hazards', 7)).toBe(
      'pnpm check lean spec --batch hazards --seeds 7 --dump',
    )
  })
})
