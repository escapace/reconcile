import assert from 'node:assert/strict'
import { reactive, toRaw } from 'vue'
import { jsonObject, oracleCorpus, type Oracle } from './lean-oracle'
import { produce } from '../src/produce'

/** Object and array drafts of Vue reactive state: an owned key, and keys the object does not own,
 * which Vue's proxy answers itself: its raw-object marker and its version of a method. */
const kinds = [
  {
    inherited: ['__v_raw', 'hasOwnProperty'],
    owned: 'a',
    make: () => ({ a: { n: 1 } }),
    write: (draft: Record<string, unknown>) => void (draft.b = 1),
  },
  {
    inherited: ['__v_raw', 'forEach'],
    owned: '0',
    make: () => [{ n: 1 }],
    write: (draft: unknown[]) => void draft.push(1),
  },
] as const

/** The source of one inherited read: the prototype's value, or the wrapper's answer. */
function inheritedSource(draft: object, base: object, key: string): string {
  const value = Reflect.get(draft, key) as unknown
  if (Object.is(value, Reflect.get(Object.getPrototypeOf(base) as object, key))) return 'prototype'
  return Object.is(value, Reflect.get(base, key)) ? 'wrapper' : 'other'
}

/** Checks one Lean row on one kind of draft. */
function checkKind(row: Record<string, unknown>, kind: (typeof kinds)[number]): void {
  const state = reactive({ value: kind.make() })
  const base = state.value as object
  produce(state, (draft) => {
    const value = draft.value as Record<string, unknown>
    if (row.copied === true) (kind.write as (draft: unknown) => void)(value)
    if (row.owned === true) {
      const child = value[kind.owned] as { n: number }
      // An own read gives the child's draft: neither Vue's proxy of it nor its raw object.
      assert.notEqual(child, Reflect.get(base, kind.owned))
      assert.notEqual(child, toRaw(base as Record<string, unknown>)[kind.owned])
      assert.equal(child.n, 1)
      assert.equal(row.source, 'own')
    } else
      for (const key of kind.inherited)
        assert.equal(inheritedSource(value, base, key), row.source, key)
    return draft
  })
}

/** Compares where draft reads come from with Lean's `DraftRead`. */
export async function checkDraftReadRuntime(oracle: Oracle): Promise<void> {
  // Before and after the first write, an owned and a not owned key.
  const rows = await oracleCorpus(oracle, 'DraftRead', 4, 64 * 1024)
  for (const line of rows) for (const kind of kinds) checkKind(jsonObject(JSON.parse(line)), kind)
  const checked = rows.length * kinds.length
  console.log(
    `Draft-read Lean/native bridge: ${checked} reads of Vue reactive object and array drafts, ` +
      'before and after the first write, come from the source Lean names',
  )
}
