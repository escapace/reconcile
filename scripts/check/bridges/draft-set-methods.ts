import assert from 'node:assert/strict'
import { jsonObject, oracleCorpus, type Oracle } from '../oracle'
import { produce } from '../../../src/produce'

const isObject = (value: unknown) => typeof value === 'object' && value !== null

const methods = [
  'union',
  'intersection',
  'difference',
  'symmetricDifference',
  'isSubsetOf',
  'isSupersetOf',
  'isDisjointFrom',
] as const

/** The operand forms: a native `Set` of the values from `current`, a native `Set` of their
 * drafts, the draft of a `Set` in `current`, and a set-like object over drafts. */
const operands = ['current', 'drafts', 'draft', 'set-like'] as const

interface Recipe {
  pool: Array<{ name: string }>
  s: Set<unknown>
  t: Set<unknown>
}

/** Maps each member of a result to its identity; a result holds this draft's object members as
 * drafts, and only union and symmetricDifference also hold the operand's keys as it gives them. */
function identifier(identities: ReadonlyMap<unknown, number>, drafts: readonly unknown[]) {
  const identify = (member: unknown, method: (typeof methods)[number]) => {
    assert.ok(identities.has(member), `unknown member ${String(member)}`)
    if (method === 'intersection' || method === 'difference')
      assert.ok(!isObject(member) || drafts.includes(member), `${method} gave a raw member`)
    return identities.get(member)
  }
  return (result: unknown, method: (typeof methods)[number]) =>
    result instanceof Set ? [...result].map((member) => identify(member, method)) : result
}

/** The operand forms over `keys`, which hold the operand's members as drafts. */
function operandForms(
  current: unknown,
  draft: unknown,
  keys: unknown[],
): Record<(typeof operands)[number], unknown> {
  return {
    current,
    draft,
    'drafts': new Set(keys),
    'set-like': {
      size: keys.length,
      has: (member: unknown) => keys.includes(member),
      keys: () => keys[Symbol.iterator](),
    },
  }
}

/** Runs every method of one Lean row on a `Set` draft, unwritten or with a working copy, against
 * each operand form, and compares the identities of the results. */
function checkRow(row: Record<string, unknown>, copied: boolean): number {
  const a = { name: 'a' }
  const b = { name: 'b' }
  const raw = [a, b, 7]
  const value = (identity: unknown) => raw[identity as number]
  const plain: Recipe = {
    pool: [a, b],
    s: new Set((row.members as unknown[]).map(value)),
    t: new Set((row.keys as unknown[]).map(value)),
  }
  const label = copied ? 'copied' : 'unwritten'
  let checked = 0
  produce(plain, (draft) => {
    const drafts = [draft.pool[0], draft.pool[1], 7]
    // Every form an object can take here: itself and its draft.
    const identities = new Map<unknown, number>([
      [7, 2],
      [a, 0],
      [b, 1],
      [drafts[0], 0],
      [drafts[1], 1],
    ])
    const identify = identifier(identities, drafts)
    if (copied) {
      draft.s.add(99)
      draft.s.delete(99)
    }
    const keys: unknown[] = (row.keys as number[]).map((identity) => drafts[identity])
    const forms = operandForms(plain.t, draft.t, keys)
    for (const operand of operands) {
      const check = (method: (typeof methods)[number]) => {
        const result = (draft.s[method] as (other: unknown) => unknown)(forms[operand])
        const where = `${label} ${operand} ${method} ${JSON.stringify(row)}`
        assert.deepEqual(identify(result, method), row[method], where)
      }
      methods.forEach(check)
      checked += methods.length
    }
    return draft
  })
  return checked
}

/** Compares `Set` draft methods with Lean's `DraftSetMethods`. */
export async function checkDraftSetMethodsRuntime(oracle: Oracle): Promise<void> {
  // Every pair of 16 member lists and 16 key lists.
  const rows = (await oracleCorpus(oracle, 'DraftSetMethods', 256, 256 * 1024)).map((line) =>
    jsonObject(JSON.parse(line)),
  )
  let checked = 0
  for (const row of rows) for (const copied of [false, true]) checked += checkRow(row, copied)
  console.log(
    `Draft-set-methods Lean/native bridge: ${checked} Set method calls on Set drafts, with four ` +
      'operand forms, give the members Lean does',
  )
}
