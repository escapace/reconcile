import { assert } from 'vitest'

/** The value that `run` throws; fails the test when `run` returns instead. */
export function thrown(run: () => unknown): unknown {
  try {
    run()
  } catch (error) {
    return error
  }
  assert.fail('expected a throw')
}
