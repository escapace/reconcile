// Differential check of `produce` and `reconcile` against native JavaScript on plain copies. The
// expected value comes only from ordinary JavaScript operations, not from the Lean models; the
// README rules that allow a difference are the policies in the fixture. A failure names its seed
// and prints the generated graph and recipe.
import { assert, it } from 'vitest'
import { produce, reconcile } from '../index'
import {
  checkProduceCase,
  checkRecipeInPlaceCase,
  checkReconcileCase,
} from './fixtures/native-differential'
import { checkCase } from './fixtures/public-api-fuzz'

const SEEDS = 3000

function runSeeds(name: string, check: (seed: number) => string | undefined): void {
  for (let seed = 1; seed <= SEEDS; seed += 1) {
    const failure = checkCase({ name, seed }, () => check(seed))
    if (failure !== undefined) assert.fail(`${name} seed ${seed}: ${failure}`)
  }
}

it(`matches native mutation of a plain copy in ${SEEDS} seeded produce recipes`, () => {
  runSeeds('produce', (seed) => checkProduceCase(seed, produce))
}, 60_000)

it(`matches a plain copy of next in ${SEEDS} seeded reconcile calls`, () => {
  runSeeds('reconcile', (seed) => checkReconcileCase(seed, reconcile))
}, 60_000)

it(`matches the produce result in ${SEEDS} seeded recipes applied in place`, () => {
  runSeeds('recipe in place', (seed) => checkRecipeInPlaceCase(seed, produce, reconcile))
}, 60_000)
