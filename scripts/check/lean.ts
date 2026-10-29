// The gate's bridges: every runtime-to-Lean bridge against one oracle process, or, for a narrowed
// run, the bridges and batches a selection names. The full run also checks the oracle protocol.
import assert from 'node:assert/strict'
import { entry } from '../framework/entry'
import { BRIDGES } from './bridges'
import type { Selection } from './bridges/selection'
import { startOracle, type Oracle } from './oracle'

/** The configuration the `lean` and `temporal` rounds and the mutation audit pass: the families
 * to run, all when empty, and what to select of a family with batches. */
export interface Config extends Selection {
  readonly families: readonly string[]
}

/** Rejected requests must not corrupt the next response or silently become passes. */
async function checkRequests(oracle: Oracle): Promise<void> {
  await assert.rejects(oracle('Unknown'), /Unknown oracle family/)
  await assert.rejects(oracle('DeferredOrder', { input: '{}' }), /expected JSON array/)
  await assert.rejects(oracle('Contract', { maxBuffer: 0 }), /Invalid oracle output limit/)
  const pending = oracle('Atoms')
  await assert.rejects(oracle('Atoms'), /open, idle session/)
  await pending
}

async function main(config: Config): Promise<number> {
  const whole = config.families.length === 0
  const bridges = whole
    ? BRIDGES
    : BRIDGES.filter((bridge) => config.families.includes(bridge.family))
  const oracle = await startOracle()
  let overflowChecked = false
  try {
    if (whole) await checkRequests(oracle.run)
    for (const bridge of bridges) await (await bridge.load())(oracle.run, config)
    if (whole) {
      // Bound a response before a whole oversized line can accumulate. Shutdown must preserve
      // the original diagnostic rather than mask it with the killed exit code.
      await assert.rejects(oracle.run('Atoms', { maxBuffer: 1 }), /output exceeds 1 bytes/)
      overflowChecked = true
    }
  } finally {
    if (overflowChecked) await assert.rejects(oracle.close(), /output exceeds 1 bytes/)
    else await oracle.close()
  }
  // A dump or the features report shows cases and fails on no difference.
  if (config.dump !== true && config.features !== true)
    console.log(`Bridges agree: ${bridges.map((bridge) => bridge.family).join(', ')}`)
  return 0
}

await entry(import.meta.filename, main)
