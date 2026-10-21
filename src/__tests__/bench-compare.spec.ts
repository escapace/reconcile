import { mkdtempSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import path from 'node:path'
import { describe, expect, it } from 'vitest'
import * as frozen from '../../perf/scenarios'
import { compareOptions, measure, workerFiles } from '../../scripts/bench-compare'
import { createBatches, scenarioNames } from '../../scripts/bench-workloads'
import { deserialize, serialize } from '../index'

describe('pnpm bench compare options', () => {
  it('covers every scenario with the budgeted defaults', () => {
    expect(compareOptions(['--baseline', 'control'])).toEqual({
      baseline: path.resolve('control'),
      candidate: path.resolve(import.meta.dirname, '../..'),
      processes: 4,
      rounds: 400,
      scenarios: [...scenarioNames],
      warmup: 40,
    })
    expect(scenarioNames).toEqual([
      'snapshot',
      'reconcile',
      'reconcile-plain-object',
      'produce',
      'serialize',
      'deserialize',
    ])
  })

  it('selects scenarios and rejects unknown ones or a missing baseline', () => {
    expect(
      compareOptions([
        '--baseline',
        'control',
        '--scenario',
        'deserialize',
        '--scenario',
        'produce',
      ]).scenarios,
    ).toEqual(['produce', 'deserialize'])
    expect(() => compareOptions(['--baseline', 'control', '--scenario', 'diag-noop'])).toThrow(
      /Unknown scenario diag-noop/,
    )
    expect(() => compareOptions([])).toThrow(/--baseline/)
    for (const [flag, value] of [
      ['--processes', '0'],
      ['--rounds', 'abc'],
      ['--warmup', '-1'],
    ])
      expect(() => compareOptions(['--baseline', 'control', `${flag}=${value}`])).toThrow(
        RangeError,
      )
  })

  it('builds a runnable batch for every scenario', () => {
    const batches = createBatches(frozen, { deserialize, serialize })
    expect(Object.keys(batches).toSorted()).toEqual([...scenarioNames].toSorted())
    for (const name of scenarioNames) batches[name]()()
    expect(() => createBatches(frozen, {}).deserialize()).toThrow(/no serialization API/)
  })

  it('reports a ratio inside its interval, oriented candidate over baseline', () => {
    const directory = mkdtempSync(path.join(tmpdir(), 'bench-compare-spec-'))
    try {
      const files = workerFiles(directory)
      const spin = (n: number) =>
        `export const batches = { x: () => () => { let s = 0; for (let i = 0; i < ${n}; i++) s += i; globalThis.sink = s } }`
      writeFileSync(files.candidate, spin(400_000))
      writeFileSync(files.baseline, spin(100_000))
      const { high, low, ratio } = measure(files, 'x', { rounds: 41, warmup: 5 }, 'baseline-first')
      expect(low).toBeLessThanOrEqual(ratio)
      expect(ratio).toBeLessThanOrEqual(high)
      expect(ratio).toBeGreaterThan(1.5)
    } finally {
      rmSync(directory, { force: true, recursive: true })
    }
  })
})
