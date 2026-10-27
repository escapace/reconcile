import { expect, it } from 'vitest'
import {
  defaultScenarioNames,
  expandRound,
  smallScenarioNames,
} from '../../scripts/bench-workloads'

it('expands a round into its scenarios', () => {
  expect(expandRound(['--out', 'x'])).toEqual(['--out', 'x'])
  expect(expandRound(['--round', 'small', '--out', 'x'])).toEqual([
    '--out',
    'x',
    ...smallScenarioNames.flatMap((name) => ['--scenario', name]),
  ])
  expect(expandRound(['--round', 'default'])).toEqual(
    defaultScenarioNames.flatMap((name) => ['--scenario', name]),
  )
  expect(() => expandRound(['--round', 'large'])).toThrow(/Unknown round large/)
})
