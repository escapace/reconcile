// The gate's bridges: every runtime-to-Lean bridge against one oracle process, or, for a narrowed
// run, the bridges and batches a selection names. The full run also checks the oracle protocol.
import assert from 'node:assert/strict'
import { entry } from '../framework/entry'
import { BRIDGES, type Bridge } from './bridges'
import { parseSeeds, type Selection } from './bridges/selection'
import { startOracle, type Oracle } from './oracle'

/** The configuration the `lean` and `temporal` rounds and the mutation audit pass: the families
 * to run, all when empty, and what to select of a family with batches, its seeds as listed. The
 * `temporal` round also requires a native Temporal, which the bridges otherwise skip. */
export interface Config extends Omit<Selection, 'seeds'> {
  readonly families: readonly string[]
  readonly seeds?: string
  readonly temporal?: boolean
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

/** The selection the bridges take: the configuration with its seeds parsed. */
function selectionOf({ seeds, ...rest }: Config): Selection {
  return { ...rest, ...(seeds === undefined ? {} : { seeds: parseSeeds(seeds) }) }
}

/** The oracle bounds a response before a whole oversized line accumulates; returns once it has
 * refused one. */
async function checkOverflow(oracle: Oracle): Promise<boolean> {
  await assert.rejects(oracle('Atoms', { maxBuffer: 1 }), /output exceeds 1 bytes/)
  return true
}

/** Closes the oracle. After an overflow its shutdown must preserve the original diagnostic rather
 * than mask it with the killed exit code. */
async function closeOracle(close: () => Promise<void>, overflowed: boolean): Promise<void> {
  if (overflowed) await assert.rejects(close(), /output exceeds 1 bytes/)
  else await close()
}

/** Runs `bridges` against one oracle; the whole gate also checks the oracle's requests and that
 * it bounds a response. */
async function runBridges(
  bridges: readonly Bridge[],
  selection: Selection,
  whole: boolean,
): Promise<void> {
  const oracle = await startOracle()
  let overflowed = false
  try {
    if (whole) await checkRequests(oracle.run)
    for (const bridge of bridges) await (await bridge.load())(oracle.run, selection)
    if (whole) overflowed = await checkOverflow(oracle.run)
  } finally {
    await closeOracle(oracle.close, overflowed)
  }
}

/** Whether the run requires a native Temporal that Node does not expose. */
const lacksTemporal = (config: Config): boolean =>
  config.temporal === true && Reflect.get(globalThis, 'Temporal') === undefined

/** The bridges of the families the configuration names, or every bridge when it names none. */
const selectedBridges = ({ families }: Config): readonly Bridge[] =>
  families.length === 0 ? BRIDGES : BRIDGES.filter((bridge) => families.includes(bridge.family))

/** Whether the run shows cases, as a dump or the features report does, and fails on no
 * difference instead of agreeing. */
const showsCases = (config: Config): boolean => config.dump === true || config.features === true

async function main(config: Config): Promise<number> {
  if (lacksTemporal(config)) {
    console.error('Node exposes no Temporal, so the bridges would skip every Temporal value.')
    return 1
  }
  const bridges = selectedBridges(config)
  await runBridges(bridges, selectionOf(config), config.families.length === 0)
  if (!showsCases(config))
    console.log(`Bridges agree: ${bridges.map((bridge) => bridge.family).join(', ')}`)
  return 0
}

await entry(import.meta.filename, main)
