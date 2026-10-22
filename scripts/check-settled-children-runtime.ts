import assert from 'node:assert/strict'
import { integerIn, jsonObject, oracleCorpus, type Oracle } from './lean-oracle'
import { DraftSession } from '../src/draft-session'
import { Finalization } from '../src/finalization'
import { produceTypes } from '../src/types/builtins'

/** The walk state a finalization keeps, read through its private fields. */
interface Internals {
  phase: { required: WeakMap<object, boolean> }
  walked: ReadonlyMap<object, readonly object[]> | undefined
}

/** Three objects whose own keys `c0`, `c1` hold the listed objects in order. */
function build(children: unknown): object[] {
  assert.ok(Array.isArray(children) && children.length === 3)
  const objects: Array<Record<string, object>> = [{}, {}, {}]
  for (const [index, list] of children.entries()) {
    assert.ok(Array.isArray(list))
    for (const [slot, child] of list.entries())
      objects[index][`c${slot}`] = objects[integerIn(child, 0, 2)]
  }
  return objects
}

/** Compares one question's answer, settled answers and kept lists with Lean's. */
function compare(
  expected: Record<string, unknown>,
  needs: boolean,
  internals: Internals,
  objects: readonly object[],
): void {
  assert.equal(needs, expected.needs, 'answer')
  const { memo, recorded } = expected
  assert.ok(Array.isArray(memo) && Array.isArray(recorded))
  for (const [index, object] of objects.entries()) {
    assert.equal(internals.phase.required.get(object) ?? null, memo[index], 'settled')
    assert.deepEqual(kept(internals, objects, object), recorded[index], 'kept children')
  }
}

/** The kept child list of `object` as object indices, or null. */
function kept(internals: Internals, objects: readonly object[], object: object): number[] | null {
  const list = internals.walked?.get(object)
  return list === undefined ? null : list.map((child) => objects.indexOf(child))
}

/** Asks whether object 0 and then object 1 need a copy, as Lean's corpus row does. */
function checkRow(row: Record<string, unknown>): boolean {
  const objects = build(row.children)
  const session = new DraftSession(produceTypes)
  const changed = integerIn(row.changed, -1, 2)
  // A write through the object's draft is a change finalization must copy.
  if (changed !== -1)
    (session.createDraft(objects[changed]) as Record<string, unknown>).written = true
  const finalization = new Finalization(session)
  const internals = finalization as unknown as Internals
  assert.ok(Array.isArray(row.answers) && row.answers.length === 2)
  compare(
    jsonObject(row.answers[0]),
    finalization.needsMaterialization(objects[0]),
    internals,
    objects,
  )
  compare(
    jsonObject(row.answers[1]),
    finalization.needsMaterialization(objects[1]),
    internals,
    objects,
  )
  return jsonObject(row.answers[1]).needs === false
}

/** Compares the finalization walk's settled answers and kept lists with
 * Lean's `Produce.SettledChildren.needs`. */
export async function checkSettledChildrenRuntime(oracle: Oracle): Promise<void> {
  // 2197 graphs of three objects with child lists of at most two entries, each with no object
  // changed or one changed.
  const rows = await oracleCorpus(oracle, 'SettledChildren', 8788, 16 * 1024 * 1024)
  let settled = 0
  for (const line of rows) if (checkRow(jsonObject(JSON.parse(line)))) settled += 1
  console.log(
    `SettledChildren Lean/native bridge: ${rows.length} graphs asked twice, answers, settled ` +
      `objects and kept child lists equal; ${settled} second answers settled unchanged`,
  )
}
