import assert from 'node:assert/strict'
import { integerIn, oracleCorpus, strictWitnesses, type Oracle } from '../oracle'
import { decodeKey } from '../fixtures/property-bridges'
import { PropertyOrder } from '../../../src/types/shared/property-publication'

const symbols = [Symbol('first'), Symbol('second')]

/** Decodes a Lean key code; labels run to 2: two index names, three names and two symbols. */
function key(code: number): PropertyKey {
  return decodeKey(code, 7, symbols)
}

function codes(value: unknown): number[] {
  assert.ok(Array.isArray(value))
  assert.ok(value.every((code) => Number.isInteger(code) && code >= 0 && code <= 7 && code !== 6))
  return value as number[]
}

/** Replays one current stream through the native cursor; true when Lean saved strict work. */
function checkTrace(observation: Record<string, unknown>): boolean {
  const desired = codes(observation.desired)
  const current = codes(observation.current)
  assert.ok(desired.length <= 3 && current.length <= 3)
  assert.equal(new Set(desired).size, desired.length)
  assert.ok(
    Array.isArray(observation.keeps) &&
      observation.keeps.every((kept) => typeof kept === 'boolean'),
  )
  const order = new PropertyOrder(
    new Map(desired.map((code) => [key(code), { node: undefined, value: 0 }])),
  )
  assert.deepEqual(
    current.map((code) => order.keep(key(code))),
    observation.keeps,
  )
  assert.equal(order.retained, integerIn(observation.retained, 0, current.length))
  assert.equal(Reflect.get(order, 'cursor'), integerIn(observation.name, 0, desired.length))
  assert.equal(Reflect.get(order, 'symbol'), integerIn(observation.symbol, -1, desired.length))
  const referenceChecks = integerIn(observation.referenceChecks, 0, 12)
  const candidateChecks = integerIn(observation.candidateChecks, 0, referenceChecks)
  return candidateChecks < referenceChecks
}

/** Compares the native cursor with executable Lean observations, not a JavaScript reference. */
export async function checkPropertyOrderRuntime(oracle: Oracle): Promise<void> {
  // The finite corpus has 157 desired permutations and 400 current streams.
  // Bound the subprocess output; unexpected growth fails rather than consuming arbitrary memory.
  const lines = await oracleCorpus(oracle, 'PropertyOrder', 62_800, 32 * 1024 * 1024)
  const strictSavings = strictWitnesses(lines, checkTrace)
  console.log(
    `Property-order Lean/native bridge: ${lines.length} traces; ${strictSavings} strict-work witnesses`,
  )
}
