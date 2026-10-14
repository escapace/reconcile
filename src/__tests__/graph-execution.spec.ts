import { assert, it } from 'vitest'
import { claimModes } from '../graph/claims'
import { advanceExecution, startExecution } from '../graph/execution'
import type { Binding, Event, Execution } from '../types'

const binding = (identity: number): Binding => ({
  choice: identity,
  construction: [],
  exposed: identity,
  fixed: false,
  mode: 0,
  palette: [0, 1, 2],
  storage: identity,
  writer: identity,
})
const event = (state: Execution, action: { tag: 'finish' | 'published' | 'reject' }): Event => ({
  ...action,
  id: state.id,
  revision: state.revision,
})
const publish = (state: Execution): Execution =>
  advanceExecution(state, event(state, { tag: 'published' }))
const check = (state: Execution, node: number): Execution =>
  advanceExecution(state, { id: state.id, node, revision: state.revision, tag: 'checked' })
const rebind = (state: Execution, mode: number): Execution =>
  advanceExecution(state, {
    exposed: 20 + mode,
    id: state.id,
    mode,
    node: 1,
    revision: state.revision,
    storage: 1,
    tag: 'rebind',
  })

it('requires publication and complete readback of the same plan and revision', () => {
  let state = startExecution(7, [binding(0), binding(1)])
  assert.equal(check(state, 0), state)
  state = publish(state)
  state = check(state, 0)
  assert.equal(advanceExecution(state, event(state, { tag: 'finish' })), state)
  const oldReceipt: Event = { id: state.id, node: 1, revision: state.revision, tag: 'checked' }
  state = rebind(state, 1)
  assert.equal(state.phase, 'publishing')
  assert.deepEqual(
    state.bindings.map((entry) => entry.writer),
    [0, 1],
  )
  assert.deepEqual(
    state.bindings.map((entry) => entry.choice),
    [0, 1],
  )
  state = publish(state)
  assert.equal(advanceExecution(state, oldReceipt), state)
  state = check(state, 1)
  assert.equal(advanceExecution(state, event(state, { tag: 'finish' })), state)
  state = check(state, 0)
  const done = advanceExecution(state, event(state, { tag: 'finish' }))
  assert.equal(done.phase, 'done')
  assert.equal(advanceExecution(done, event(done, { tag: 'reject' })), done)
  const next = publish(startExecution(8, [binding(0), binding(1)]))
  assert.equal(advanceExecution(next, oldReceipt), next)
  // The reducer owns mutable checked membership: object identity alone cannot
  // establish that a receipt from another plan had no effect.
  assert.equal(next.phase, 'checking')
  if (next.phase === 'checking') assert.equal(next.checked.size, 0)
})

it('consumes finite exposure options without changing the selected write receiver', () => {
  let state = publish(startExecution(0, [binding(0), binding(1)]))
  state = publish(rebind(state, 1))
  state = publish(rebind(state, 2))
  assert.equal(state.phase, 'checking')
  assert.equal(state.bindings[1].writer, 1)
  assert.equal(state.bindings[1].exposed, 22)
  assert.equal([...claimModes(state.claims[1])].length, 3)
  assert.equal(rebind(state, 1).phase, 'rejected')
  assert.equal(rebind(state, 3).phase, 'rejected')
})

it('keeps out-of-mask exposure labels distinct and rejects their repeated use', () => {
  const choices = [binding(0), { ...binding(1), palette: [0, 30, 31, 32, 2 ** 32] }]
  let state = publish(startExecution(0, choices))
  for (const mode of [30, 31, 32, 2 ** 32]) {
    state = publish(rebind(state, mode))
    assert.equal(state.phase, 'checking')
    assert.equal(state.bindings[1].mode, mode)
  }
  assert.equal([...claimModes(state.claims[1])].length, 5)
  assert.equal(rebind(state, 31).phase, 'rejected')
})

it('rejects fixed, storage-changing and construction-invalidating rebindings', () => {
  const fixed = publish(startExecution(0, [binding(0), { ...binding(1), fixed: true }]))
  assert.equal(rebind(fixed, 1).phase, 'rejected')
  const view = { ...binding(0), construction: [{ identity: 1, node: 1 }] }
  const constructed = publish(startExecution(0, [view, binding(1)]))
  assert.equal(rebind(constructed, 1).phase, 'rejected')
  const ordinary = publish(startExecution(0, [binding(0), binding(1)]))
  assert.equal(
    advanceExecution(ordinary, {
      exposed: 21,
      id: 0,
      mode: 1,
      node: 1,
      revision: 0,
      storage: 2,
      tag: 'rebind',
    }).phase,
    'rejected',
  )
  assert.equal(check(ordinary, 10), ordinary)
})

it('counts distinct checked nodes beyond byte range and resets membership on a new revision', () => {
  const size = 513
  let state = publish(
    startExecution(
      9,
      Array.from({ length: size }, (_, node) => binding(node)),
    ),
  )
  for (let node = size - 1; node > 0; node -= 1) {
    state = check(state, node)
    state = check(state, node)
  }
  assert.equal(advanceExecution(state, event(state, { tag: 'finish' })).phase, 'checking')
  assert(state.phase === 'checking')
  assert.equal(state.checked.size, size - 1)
  assert.equal([...state.checked].length, size - 1)
  state = publish(rebind(state, 1))
  assert(state.phase === 'checking')
  assert.equal(state.checked.size, 0)
  for (let node = 0; node < size; node += 1) state = check(state, node)
  assert.equal(advanceExecution(state, event(state, { tag: 'finish' })).phase, 'done')
})
