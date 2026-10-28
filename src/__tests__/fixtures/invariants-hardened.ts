// Child-process driver for standard-prototypes.spec.ts: a sample of the documented contracts
// on random graphs, run under `node --frozen-intrinsics` and under SES `lockdown`, where every
// standard prototype is frozen and some of its properties are accessors.
import {
  produceInvariants,
  reconcileInvariants,
  serializeInvariants,
  snapshotInvariants,
  writeFreeInvariants,
} from './public-api-invariants'

const OPTIONS = { accessors: true, attributes: true, nodes: 60, reorder: true, same: true }
const PLAIN = { nodes: 60, reorder: true }
const SEEDS = 40

export function run(): { cases: number; failures: string[] } {
  const failures: string[] = []
  let cases = 0
  const check = (name: string, seed: number, result: string[] | undefined): void => {
    if (result === undefined) return
    cases += 1
    failures.push(...result.map((f) => `${name} seed ${seed}: ${f}`))
  }
  for (let seed = 1; seed <= SEEDS; seed += 1) {
    check('reconcile', seed, reconcileInvariants(seed, OPTIONS))
    check('write-free', seed, writeFreeInvariants(seed, OPTIONS))
    check('produce', seed, produceInvariants(seed, { ...PLAIN, accessors: true, attributes: true }))
    check(
      'snapshot',
      seed,
      snapshotInvariants(seed, { ...PLAIN, accessors: true, attributes: true }),
    )
    check('serialize', seed, serializeInvariants(seed, PLAIN))
  }
  return { cases, failures }
}
