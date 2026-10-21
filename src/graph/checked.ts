import type { CheckedSet } from '../types'
import { Detached } from '../standard-prototypes'

/** Call-owned membership for one publication revision; node IDs remain ordinary numbers. */
export class CheckedNodes extends Detached implements CheckedSet {
  declare private count: number
  declare private readonly marks: Uint8Array

  constructor(size: number) {
    super()
    this.count = 0
    this.marks = new Uint8Array(size)
  }

  get size(): number {
    return this.count
  }

  /** The execution reducer supplies a valid node in this revision's domain. */
  add(node: number): void {
    if (this.marks[node] === 0) {
      this.marks[node] = 1
      this.count += 1
    }
  }

  *[Symbol.iterator](): IterableIterator<number> {
    for (let node = 0; node < this.marks.length; node += 1) if (this.marks[node] !== 0) yield node
  }
}
