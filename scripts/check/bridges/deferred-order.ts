import assert from 'node:assert/strict'
import type { deferredKeys, deferredOrderCases } from '../fixtures/deferred-order-cases'
import { bundleWithHooks, type Hook } from '../../esbuild'
import type { Oracle } from '../oracle'
import { keyCode } from '../fixtures/property-bridges'
import type { canPublishProperties } from '../../../src/types/shared/property-publication'

const RECORDER = '__reconcileCursor'

/** The preflight's checkpoints, after which the recorder runs. */
const HOOKS: readonly Hook[] = [
  [
    '  const previous = surface.keys(current, node)\n',
    `globalThis.${RECORDER}.start(previous, desiredKeys, surface.ordered)\n`,
  ],
  [
    '    const retained = order?.through(previous, key)\n',
    `globalThis.${RECORDER}.fixed(order, retained, key)\n`,
  ],
  ['  order?.through(previous)\n', `globalThis.${RECORDER}.final(order)\n`],
]

/** The cursor and the cases from one bundle, so both share the library's modules. */
interface Instrumented {
  canPublishProperties: typeof canPublishProperties
  deferredKeys: typeof deferredKeys
  deferredOrderCases: typeof deferredOrderCases
}

interface Order {
  retained: number
}

/** One preflight's trace: the oracle's input and the cursor's state at each demand. */
interface Trace {
  demands: number[]
  desired: PropertyKey[]
  finals: boolean[]
  observations: Array<[number, number | null] | null>
  ordered: boolean
  previous: PropertyKey[]
}

/** Records the trace of each preflight into the latest one `traces` holds. */
function recorder(traces: Trace[]) {
  const last = (): Trace => traces[traces.length - 1]
  return {
    final(order: Order | undefined) {
      last().demands.push(last().previous.length)
      last().finals.push(true)
      last().observations.push(order === undefined ? null : [order.retained, null])
    },
    fixed(order: Order | null | undefined, retained: number, key: PropertyKey) {
      last().demands.push(last().previous.indexOf(key) + 1)
      last().finals.push(false)
      last().observations.push(order == null ? null : [order.retained, retained])
    },
    start(previous: readonly PropertyKey[], desired: readonly PropertyKey[], ordered: boolean) {
      const lists = { demands: [], finals: [], observations: [] }
      traces.push({ ...lists, desired: [...desired], ordered, previous: [...previous] })
    },
  }
}

/** The production cursor, instrumented at its checkpoints, runs every case; its traces go to the
 * oracle as inputs and its observations are compared with the oracle's. */
export async function checkDeferredOrderRuntime(oracle: Oracle): Promise<void> {
  const library = (await bundleWithHooks(
    "export { canPublishProperties } from './src/types/shared/property-publication'\n" +
      "export { deferredKeys, deferredOrderCases } from './scripts/check/fixtures/deferred-order-cases'",
    /property-publication\.ts$/,
    HOOKS,
  )) as Instrumented
  // Integer keys, names and symbols by class, labelled by their index; `length` is a name of its
  // own.
  const code = (key: PropertyKey): number => {
    if (key === 'length') return keyCode(1, 6)
    const id = library.deferredKeys.indexOf(key)
    assert.ok(id >= 0)
    return keyCode(id < 2 ? 0 : id < 4 ? 1 : 2, id)
  }
  const traces: Trace[] = []
  const errors: boolean[] = []
  Reflect.set(globalThis, RECORDER, recorder(traces))
  try {
    library.deferredOrderCases((input) => {
      const started = traces.length
      let error: unknown
      try {
        library.canPublishProperties(input.node, input.current, input.surface, [])
      } catch (caught) {
        error = caught
      }
      assert.equal(error, input.failure, input.name)
      assert.equal(traces.length, started + 1, input.name)
      errors.push(error !== undefined)
    })
  } finally {
    Reflect.deleteProperty(globalThis, RECORDER)
  }
  const inputs = traces.map(({ demands, desired, finals, ordered, previous }) => ({
    demands,
    desired: desired.map(code),
    finals,
    ordered,
    previous: previous.map(code),
  }))
  const expected: unknown = JSON.parse(
    await oracle('DeferredOrder', { input: JSON.stringify(inputs), maxBuffer: 16 * 1024 * 1024 }),
  )
  assert.deepEqual(
    traces.map((trace) => trace.observations),
    expected,
  )
  const checkpoints = traces.reduce((sum, trace) => sum + trace.observations.length, 0)
  console.log(
    `Deferred-order bridge: ${traces.length} actual preflights, ${checkpoints} demanded ` +
      `checkpoints, ${errors.filter(Boolean).length} original error identities.`,
  )
}
