import type { CheckedSet } from '../types'
import { Detached } from '../standard-prototypes'

// Membership of up to this many nodes is a bit mask, without a byte array.
const MASK_NODES = 31

/** Call-owned membership for one publication revision; node IDs remain ordinary numbers. */
export class CheckedNodes extends Detached implements CheckedSet {
  declare private bits: number
  declare private count: number
  declare private readonly marks: Uint8Array | undefined

  constructor(size: number) {
    super()
    this.bits = 0
    this.count = 0
    this.marks = size <= MASK_NODES ? undefined : new Uint8Array(size)
  }

  get size(): number {
    return this.count
  }

  /** The execution reducer supplies a valid node in this revision's domain. */
  add(node: number): void {
    const marks = this.marks
    if (marks === undefined) {
      if ((this.bits & (1 << node)) === 0) {
        this.bits |= 1 << node
        this.count += 1
      }
    } else if (marks[node] === 0) {
      marks[node] = 1
      this.count += 1
    }
  }

  *[Symbol.iterator](): IterableIterator<number> {
    const marks = this.marks
    if (marks === undefined) {
      for (let node = 0; node < MASK_NODES; node += 1)
        if ((this.bits & (1 << node)) !== 0) yield node
    } else for (let node = 0; node < marks.length; node += 1) if (marks[node] !== 0) yield node
  }
}
