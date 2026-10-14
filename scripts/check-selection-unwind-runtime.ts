// Reference backtracking transitions composed from current selector operations.
// This does not execute an installed bulk tier-exit implementation.
import assert from 'node:assert/strict'
import { addIncoming } from '../src/graph/incoming-consensus'
import type { Choice, IncomingConsensus } from '../src/types'
import type { Oracle } from './lean-oracle'

interface Frame {
  choice: Choice
  followers: number[]
  node: number
}
interface Input {
  forceOwners: number[]
  frames: Frame[]
  keep: number
}
interface Observation {
  demands: number[][]
  forced: number[]
  owners: number[]
  retained: number
  trail: Array<[number, number[]]>
}
type Transitions = [assignments: Observation[], undos: Observation[]]

const summary = (value: IncomingConsensus): number[] =>
  value === undefined ? [] : value === null ? [0, 0] : [value as number]

const ascending = (values: Iterable<number>): number[] => [...values].sort((a, b) => a - b)

/** Requirements on later nodes: only these update incoming demand summaries. */
const forwardEdges = (frame: Frame) =>
  frame.choice.required.filter((requirement) => requirement.node > frame.node)

/** Selector state composed from the runtime demand summary, with an undo trail. */
class ReferenceSelector {
  private readonly demands: IncomingConsensus[]
  private readonly forced = new Map<number, number>()
  private readonly owners = new Set<number>()
  private retained = 0
  private readonly trail: Array<[number, IncomingConsensus]> = []

  constructor(
    private readonly forceOwners: readonly number[],
    width: number,
  ) {
    this.demands = new Array<IncomingConsensus>(width)
  }

  assign(frame: Frame): void {
    assert.ok(!this.owners.has(frame.choice.storage as number))
    for (const member of frame.followers) assert.ok(!this.forced.has(this.owner(member)))
    for (const edge of forwardEdges(frame)) {
      this.trail.push([edge.node, this.demands[edge.node]])
      this.demands[edge.node] = addIncoming(this.demands[edge.node], edge.identity)
    }
    for (const member of frame.followers) this.forced.set(this.owner(member), member)
    this.owners.add(frame.choice.storage as number)
    this.retained += Number(frame.choice.retained)
  }

  observe(): Observation {
    return {
      demands: Array.from(this.demands, summary),
      forced: ascending(this.forced.values()),
      owners: ascending(this.owners),
      retained: this.retained,
      trail: this.trail.toReversed().map(([node, old]) => [node, summary(old)]),
    }
  }

  undo(frame: Frame): void {
    for (const member of frame.followers) this.forced.delete(this.owner(member))
    for (const requirement of forwardEdges(frame).toReversed()) {
      const [node, old] = this.trail.pop()!
      assert.equal(node, requirement.node)
      this.demands[node] = old
    }
    this.owners.delete(frame.choice.storage as number)
    this.retained -= Number(frame.choice.retained)
  }

  private owner(literal: number): number {
    return this.forceOwners[literal] ?? literal
  }
}

function observeTransitions(input: Input): Transitions {
  const width =
    1 +
    Math.max(0, ...input.frames.flatMap((f) => [f.node, ...f.choice.required.map((r) => r.node)]))
  const selector = new ReferenceSelector(input.forceOwners, width)
  const assignments = [selector.observe()]
  for (const frame of input.frames) {
    selector.assign(frame)
    assignments.push(selector.observe())
  }
  const undos = [selector.observe()]
  for (const frame of input.frames.slice(input.keep).toReversed()) {
    selector.undo(frame)
    undos.push(selector.observe())
  }
  assert.deepEqual(undos.at(-1), assignments[input.keep])
  return [assignments, undos]
}

function prefixFrames(length: number, variant: number): Frame[] {
  return Array.from({ length }, (_, node) => ({
    choice: {
      identity: node + 10,
      required: [
        { identity: node + 10, node },
        { identity: 10, node: 0 },
        { identity: 21, node: length + 1 },
        { identity: variant < 2 ? 21 : node + 21, node: length + 1 },
        { identity: 30, node: node + 1 },
      ],
      retained: (node + variant) % 3 !== 0,
      storage: node + 40,
    },
    followers: node % 2 === 0 ? [(node + 1) * 2 + (variant % 2)] : [],
    node,
  }))
}

/** Every kept prefix of frames with duplicate and conflicting demands. */
function admittedPrefixes(): Input[] {
  const inputs: Input[] = []
  for (let length = 0; length <= 8; length += 1) {
    for (let variant = 0; variant < 4; variant += 1) {
      const frames = prefixFrames(length, variant)
      for (let keep = 0; keep <= length; keep += 1)
        inputs.push({
          forceOwners: Array.from({ length: 20 }, (_, literal) => Math.floor(literal / 2)),
          frames,
          keep,
        })
    }
  }
  return inputs
}

/** Lean reports owner and forced sets unordered; compare them as sorted lists. */
function normalize(transitions: Transitions): void {
  for (const states of transitions)
    for (const state of states) {
      state.owners.sort((a, b) => a - b)
      state.forced.sort((a, b) => a - b)
    }
}

export async function checkSelectionUnwindRuntime(oracle: Oracle): Promise<void> {
  const inputs = admittedPrefixes()
  const malformed: Input = {
    forceOwners: [0, 0],
    frames: [0, 1].map((node) => ({
      choice: { identity: node, required: [], retained: true, storage: node },
      followers: [node],
      node,
    })),
    keep: 0,
  }
  await assert.rejects(
    oracle('SelectionUnwind', [], { input: JSON.stringify([malformed]) }),
    /Invalid unwind admission/,
  )
  const frozen = JSON.stringify(inputs)
  const results = JSON.parse(
    await oracle('SelectionUnwind', [], { input: frozen }),
  ) as Transitions[]
  assert.equal(results.length, inputs.length)
  let transitions = 0
  for (const [index, input] of inputs.entries()) {
    normalize(results[index])
    const expected = observeTransitions(input)
    assert.deepEqual(results[index], expected, `unwind transitions ${index}`)
    transitions += expected[0].length + expected[1].length - 2
  }
  assert.equal(JSON.stringify(inputs), frozen)
  console.log(
    `Selection-unwind bridge: ${inputs.length} admitted prefixes, ${transitions} assignment/undo ` +
      'transitions with duplicate/conflicting demands, disjoint forced followers and older prefix restoration.',
  )
}
