import { assert, describe, it } from 'vitest'
import {
  adversarialInvariants,
  produceInvariants,
  reconcileInvariants,
  serializeInvariants,
  snapshotInvariants,
  writeFreeInvariants,
} from './fixtures/public-api-invariants'
import { runDriver } from './fixtures/run-driver'

// The documented contracts, checked on seeded random graphs far larger than the Spec bridge's
// and without a reference; the checks are in `fixtures/public-api-invariants.ts`.

const OPTIONS = { accessors: true, attributes: true, nodes: 120, reorder: true, same: true }
const PLAIN = { nodes: 120, reorder: true }
const SEEDS = 300

/** Runs `check` over the seeds; a check that returns undefined was rejected and does not count. */
function over(check: (seed: number) => string[] | undefined, least = 0): void {
  let cases = 0
  for (let seed = 1; seed <= SEEDS; seed += 1) {
    const failures = check(seed)
    if (failures === undefined) continue
    cases += 1
    assert.deepEqual(failures, [], `seed ${seed}`)
  }
  assert.ok(cases >= least, `${cases} cases succeeded`)
}

describe('reconcile on large random graphs', () => {
  it('reaches the shape of next, keeps objects at their own positions and keeps attributes', () => {
    over((seed) => reconcileInvariants(seed, OPTIONS), SEEDS / 2)
  })

  it('writes nothing for a next equal to current', () => {
    over((seed) => writeFreeInvariants(seed, OPTIONS), SEEDS / 2)
  })

  it('rejects or reaches the shape of next when setters change other objects', () => {
    let armed = 0
    let succeeded = 0
    for (let seed = 1; seed <= SEEDS; seed += 1) {
      const outcome = adversarialInvariants(seed, OPTIONS, 'setters')
      armed += outcome.armed
      if (!outcome.rejected) succeeded += 1
      assert.deepEqual(outcome.failures, [], `seed ${seed}`)
    }
    assert.ok(
      armed > SEEDS / 2 && succeeded > SEEDS / 4,
      `${armed} setters armed, ${succeeded} succeeded`,
    )
  })
})

describe('produce, snapshot and serialize on large random graphs', () => {
  it('produce returns current for a recipe that changes nothing', () => {
    over((seed) => produceInvariants(seed, { ...PLAIN, accessors: true, attributes: true }))
  })

  it('snapshot is a detached copy with the same shape', () => {
    over((seed) => snapshotInvariants(seed, { ...PLAIN, accessors: true, attributes: true }))
  })

  it('serialize round-trips supported graphs and rejects the others', () => {
    over((seed) => serializeInvariants(seed, PLAIN))
  })
})

describe('in hardened runtimes', () => {
  it('holds under node --frozen-intrinsics', async () => {
    const output = await runDriver('invariants-hardened.ts', ['--frozen-intrinsics'])
    assert.ok(output.cases > 100, `${output.cases} cases`)
    assert.deepEqual(output.failures, [])
  })

  it('holds under SES lockdown with severe override taming', async () => {
    const output = await runDriver('invariants-hardened.ts', [], {
      order: 'after',
      taming: 'severe',
    })
    assert.ok(output.frozen && output.cases > 100, `${output.cases} cases`)
    assert.deepEqual(output.failures, [])
  })
})
