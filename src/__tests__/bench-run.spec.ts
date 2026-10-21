import { describe, expect, it } from 'vitest'
import { createBenchmarks, selectedScenarios } from '../../scripts/bench-run'
import { scenarioNames } from '../../scripts/bench-workloads'

describe('Tinybench runner', () => {
  it('registers all frozen scenario pairs with the original sampling settings', () => {
    const benchmarks = [...createBenchmarks()].map(({ bench }) => bench)
    expect(
      benchmarks.map((benchmark) => [benchmark.name, benchmark.tasks.map((task) => task.name)]),
    ).toEqual([
      ['snapshot', ['snapshot', 'structuredClone reference']],
      ['reconcile', ['detached clone reference', 'reconcile']],
      ['reconcilePlainObject', ['detached clone reference', 'reconcilePlainObject']],
      ['produce vs immer shared draft surface', ['immer produce', 'produce']],
      [
        'serialize',
        [
          'JSON.stringify json-1000 (reference)',
          'binary-64k',
          'cycle-300',
          'dag-2000',
          'deep-200',
          'json-1000',
          'rich',
        ],
      ],
      [
        'deserialize',
        [
          'JSON.parse json-1000 (reference)',
          'binary-64k',
          'cycle-300',
          'dag-2000',
          'deep-200',
          'json-1000',
          'rich',
        ],
      ],
    ])
    for (const benchmark of benchmarks) {
      expect(benchmark).toMatchObject({
        concurrency: null,
        iterations: 500,
        throws: true,
        time: 500,
        warmup: true,
        warmupIterations: 5,
        warmupTime: 100,
      })
    }
  })

  it('selects scenarios by name, in library order', () => {
    expect(
      [...createBenchmarks(['deserialize', 'snapshot'])].map(({ scenario }) => scenario),
    ).toEqual(['snapshot', 'deserialize'])
    expect(selectedScenarios([])).toEqual([...scenarioNames])
    expect(selectedScenarios(['--scenario', 'deserialize'])).toEqual(['deserialize'])
    expect(() => selectedScenarios(['--scenario', 'diag-noop'])).toThrow(/Unknown scenario/)
  })

  it('propagates task failures instead of reporting successful measurements', () => {
    const benchmark = createBenchmarks(['snapshot']).next().value?.bench
    expect(benchmark).toBeDefined()
    if (benchmark === undefined) throw new Error('Missing benchmark')
    for (const task of benchmark.tasks) benchmark.remove(task.name)
    const failure = new Error('scenario failed')
    benchmark.add(
      'failure',
      () => {
        throw failure
      },
      { async: false },
    )
    expect(() => benchmark.runSync()).toThrow(failure)
  })
})
