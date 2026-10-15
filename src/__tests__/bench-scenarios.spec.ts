import { describe, expect, it } from 'vitest'
import { createBenchmarks } from '../../scripts/bench-scenarios'

describe('Tinybench runner', () => {
  it('registers all frozen scenario pairs with the original sampling settings', () => {
    const benchmarks = [...createBenchmarks()]
    expect(
      benchmarks.map((benchmark) => [benchmark.name, benchmark.tasks.map((task) => task.name)]),
    ).toEqual([
      ['produce vs immer shared draft surface', ['immer produce', 'produce']],
      ['reconcile', ['detached clone reference', 'reconcile']],
      ['reconcilePlainObject', ['detached clone reference', 'reconcilePlainObject']],
      ['snapshot', ['baseline', 'snapshot']],
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

  it('propagates task failures instead of reporting successful measurements', () => {
    const benchmark = createBenchmarks().next().value
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
