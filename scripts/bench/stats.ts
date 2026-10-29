// The statistics of an A/B round, ported from the Python driver it replaces so that a round
// reads the same: Python's seeded generator, median and bootstrap draw identical numbers.

/** Python's `random.Random`: MT19937 seeded from an integer, and `random()`. */
class PythonRandom {
  private index = 624
  private readonly state = new Uint32Array(624)

  constructor(seed: number) {
    // Python seeds from the 32-bit words of the seed's absolute value, least significant first.
    const key: number[] = []
    for (let rest = Math.abs(seed); key.length === 0 || rest > 0; rest = Math.floor(rest / 2 ** 32))
      key.push(rest % 2 ** 32)
    this.seedByArray(key)
  }

  private seedWith(seed: number): void {
    const mt = this.state
    mt[0] = seed
    for (let index = 1; index < 624; index += 1) {
      const previous = mt[index - 1] ^ (mt[index - 1] >>> 30)
      mt[index] = Math.imul(1_812_433_253, previous) + index
    }
  }

  private seedByArray(key: readonly number[]): void {
    this.seedWith(19_650_218)
    const mt = this.state
    let index = 1
    let position = 0
    for (let count = Math.max(624, key.length); count > 0; count -= 1) {
      const previous = mt[index - 1] ^ (mt[index - 1] >>> 30)
      mt[index] = (mt[index] ^ Math.imul(previous, 1_664_525)) + key[position] + position
      index += 1
      position += 1
      if (index >= 624) {
        mt[0] = mt[623]
        index = 1
      }
      if (position >= key.length) position = 0
    }
    for (let count = 623; count > 0; count -= 1) {
      const previous = mt[index - 1] ^ (mt[index - 1] >>> 30)
      mt[index] = (mt[index] ^ Math.imul(previous, 1_566_083_941)) - index
      index += 1
      if (index >= 624) {
        mt[0] = mt[623]
        index = 1
      }
    }
    mt[0] = 0x80_00_00_00
  }

  private twist(): void {
    const mt = this.state
    for (let index = 0; index < 624; index += 1) {
      const y = (mt[index] & 0x80_00_00_00) | (mt[(index + 1) % 624] & 0x7f_ff_ff_ff)
      mt[index] = mt[(index + 397) % 624] ^ (y >>> 1) ^ ((y & 1) === 1 ? 0x99_08_b0_df : 0)
    }
    this.index = 0
  }

  private next(): number {
    if (this.index >= 624) this.twist()
    let y = this.state[this.index]
    this.index += 1
    y ^= y >>> 11
    y ^= (y << 7) & 0x9d_2c_56_80
    y ^= (y << 15) & 0xef_c6_00_00
    y ^= y >>> 18
    return y >>> 0
  }

  /** A float in [0, 1) from 53 random bits, as Python's `random()`. */
  random(): number {
    const high = this.next() >>> 5
    const low = this.next() >>> 6
    return (high * 67_108_864 + low) / 9_007_199_254_740_992
  }
}

/** Python's `statistics.median`. */
export function median(values: readonly number[]): number {
  const sorted = values.toSorted((left, right) => left - right)
  const middle = Math.floor(sorted.length / 2)
  return sorted.length % 2 === 1 ? sorted[middle] : (sorted[middle - 1] + sorted[middle]) / 2
}

const MIN_INTERVAL_PAIRS = 10

/** Bootstrap 90% interval of the median paired change, with a fixed seed, as the Python driver drew
 * it. Fewer than `MIN_INTERVAL_PAIRS` pairs give no interval. */
export function interval(changes: readonly number[], draws = 2000): [number, number] | undefined {
  if (changes.length < MIN_INTERVAL_PAIRS) return undefined
  const generator = new PythonRandom(0x9e_37_79_b9)
  const medians: number[] = []
  for (let draw = 0; draw < draws; draw += 1) {
    const sample: number[] = []
    for (let index = 0; index < changes.length; index += 1)
      sample.push(changes[Math.floor(generator.random() * changes.length)])
    medians.push(median(sample))
  }
  medians.sort((left, right) => left - right)
  return [medians[Math.trunc(draws * 0.05)], medians[Math.trunc(draws * 0.95) - 1]]
}

/** A faster reading needs at least this median gain, in percent. */
export const GAIN_PERCENT = 2
/** A slower reading needs a median beyond this guard, in percent. */
export const GUARD_PERCENT = 3

export type Reading =
  'faster' | 'slightly faster' | 'slightly slower' | 'slower' | 'too few pairs' | 'unresolved'

/** Classifies one round. A resolved change, whose interval excludes zero, reads faster or slower
 * beyond the gain or guard and slightly faster or slower within them. */
export function reading(median: number, bounds: readonly [number, number] | undefined): Reading {
  if (bounds === undefined) return 'too few pairs'
  if (bounds[1] < 0) return median <= -GAIN_PERCENT ? 'faster' : 'slightly faster'
  if (bounds[0] > 0) return median >= GUARD_PERCENT ? 'slower' : 'slightly slower'
  return 'unresolved'
}

/** Python's `round`, which rounds halves to even. */
export function roundHalfEven(value: number): number {
  const floor = Math.floor(value)
  const fraction = value - floor
  if (fraction !== 0.5) return Math.round(value)
  return floor % 2 === 0 ? floor : floor + 1
}

/** The batches and warmup batches of the short run of every bundle before a round. */
export const PREFLIGHT = { batches: 5, warmup: 5 } as const

/** One timed run of a harness. */
export interface Sample {
  readonly elapsedMs: number
  readonly scenario: string
  readonly wallSeconds: number
}

export interface Counts {
  readonly batches: number
  readonly warmup: number
}

/**
 * Batches and warmup per scenario: explicit counts, or enough for `seconds` of measured work at
 * the faster tree's preflight batch time (at least 20), with half as many warmup batches. A
 * preflight still runs partly cold, so its batch time is an upper bound.
 */
export function batchCounts(
  preflight: readonly Sample[],
  batches: number | 'auto',
  warmup: number | 'auto',
  seconds: number,
): Record<string, Counts> {
  const counts: Record<string, Counts> = {}
  for (const scenario of new Set(preflight.map((sample) => sample.scenario))) {
    const batch = Math.min(
      ...preflight
        .filter((sample) => sample.scenario === scenario)
        .map((sample) => sample.elapsedMs / 1000 / PREFLIGHT.batches),
    )
    const measured = batches === 'auto' ? Math.max(20, roundHalfEven(seconds / batch)) : batches
    counts[scenario] = {
      batches: measured,
      warmup: warmup === 'auto' ? Math.floor(measured / 2) : warmup,
    }
  }
  return counts
}

/** The sampling time of a round predicted from its preflight runs. */
export function estimateSeconds(
  preflight: readonly Sample[],
  pairs: number,
  counts: Readonly<Record<string, Counts>>,
): number {
  let total = 0
  for (const sample of preflight) {
    const loop = sample.elapsedMs / 1000
    const count = counts[sample.scenario]
    const startup =
      sample.wallSeconds - (loop * (PREFLIGHT.batches + PREFLIGHT.warmup)) / PREFLIGHT.batches
    total += Math.max(startup, 0) + (loop / PREFLIGHT.batches) * (count.batches + count.warmup)
  }
  return total * pairs
}
