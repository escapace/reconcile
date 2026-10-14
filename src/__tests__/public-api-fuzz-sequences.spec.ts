import { assert, describe, it } from 'vitest'
import { reactive } from 'vue'
import { produce, reconcile, ReconcileError, snapshot } from '../index'
import {
  randomSource,
  checkCase,
  graphsEqual,
  sequenceFixture,
  runSequence,
  keyFixture,
  runKeySequence,
  operationOutcome,
  physicalCopy,
  observedDescriptors,
  keySequences,
  orderedObject,
} from './fixtures/public-api-fuzz'

// Split from one file so both test workers share the fuzz corpus; every case, seed and
// deadline is unchanged.
describe('deterministic public API fuzz regressions', () => {
  it.each([false, true])(
    'matches native edit sequences with Vue wrapping = %s',
    (wrapped) => {
      const random = randomSource(0x92_01_73, 8)
      const trials = wrapped ? 2000 : 5000
      for (let trial = 0; trial < trials; trial += 1) {
        checkCase({ seed: random.seed, trial, wrapped }, () => {
          const operations = Array.from({ length: 25 }, () => [
            random.next(24),
            random.next(10),
            random.next(20),
          ])
          const raw = sequenceFixture()
          const current = wrapped ? reactive(raw) : raw
          const before = wrapped ? snapshot(current) : structuredClone(current)
          const expected = (
            wrapped ? snapshot(current) : structuredClone(current)
          ) as typeof current
          runSequence(expected, operations)
          const result = produce(current, (draft) => runSequence(draft, operations))
          assert.isTrue(graphsEqual(before, wrapped ? snapshot(current) : current))
          assert.isTrue(graphsEqual(expected, result))
          assert.isTrue(graphsEqual(expected, snapshot(result)))
          const published = reconcile(current, result)
          assert.equal(published, current)
          assert.isTrue(graphsEqual(expected, published))
        })
      }
    },
    60_000,
  )

  it('matches 2,000 native Vue sequences of 30 raw, wrapped, and draft-key operations', () => {
    const random = randomSource(438_772, 8)
    for (let trial = 0; trial < 2000; trial += 1) {
      checkCase({ seed: random.seed, trial }, () => {
        const operations = Array.from({ length: 30 }, () => [
          random.next(7),
          random.next(2),
          random.next(3),
          random.next(10),
        ])
        const a = keyFixture()
        const b = keyFixture()
        const before = snapshot(a.root)
        const expected = runKeySequence(b.root, b.raw, operations)
        let trace: unknown[] = []
        const result = produce(a.root, (draft) => {
          trace = runKeySequence(draft, a.raw, operations)
          return draft
        })
        assert.deepEqual(trace, expected)
        assert.isTrue(graphsEqual(b.root, result))
        assert.isTrue(graphsEqual(before, a.root))
        const published = reconcile(a.root, result)
        assert.equal(published, a.root)
        assert.isTrue(graphsEqual(b.root, published))
      })
    }
  }, 60_000)

  // Compare recipe-time reflection and failures against an independently mutated
  // native counterpart, wrapped in Vue in the Vue lane. Array metadata outside
  // indexed elements is tested here as draft state, not as a finalization promise.
  it.each([false, true])(
    'matches 90,000 native descriptor transitions and reentrant truncations with Vue wrapping = %s',
    (wrapped) => {
      const random = randomSource(0x27_18_28_18)
      let operations = 0
      for (let trial = 0; trial < 3000; trial += 1) {
        operations += checkCase({ seed: random.seed, trial, wrapped }, () => {
          const array = trial % 2 === 0
          const base: object = array ? new Array<unknown>(5) : (Object.create(null) as object)
          for (let index = 0; index < 5; index += 1) {
            if (random.next(3) !== 0) {
              // Keep PRNG draws in the original writable/configurable/enumerable order.
              const writable = Boolean(random.next(2))
              const configurable = Boolean(random.next(2))
              const enumerable = Boolean(random.next(2))
              Object.defineProperty(base, array ? String(index) : `k${index}`, {
                configurable,
                enumerable,
                value: index,
                writable,
              })
            }
          }
          if (array && random.next(4) === 0)
            Object.defineProperty(base, 'length', { writable: false })
          const copy = physicalCopy(base)
          const native = wrapped ? reactive(copy) : copy
          const current = wrapped ? reactive(base) : base
          const before = observedDescriptors(current)
          produce(current, (draft) => {
            for (let step = 0; step < 30; step += 1) {
              const keys = array
                ? ['0', '1', '2', '3', '4', '5', 'length', '-0', '01', '4294967295', '__proto__']
                : ['k0', 'k1', 'k2', 'k3', 'k4', 'k5', '__proto__', '0', 'length']
              const key = keys[random.next(keys.length)]
              const remove = random.next(4) === 0
              const value =
                key === 'length' && array
                  ? [0, 1, 2, 3, 5, 7, -1, 2.5, Number.NaN, '2', undefined, 0n][random.next(12)]
                  : random.next(20)
              const expected = operationOutcome(() =>
                remove ? Reflect.deleteProperty(native, key) : Reflect.set(native, key, value),
              )
              const actual = operationOutcome(() =>
                remove ? Reflect.deleteProperty(draft, key) : Reflect.set(draft, key, value),
              )
              assert.deepEqual(actual, expected, `outcome step=${step} key=${key}`)
              assert.deepEqual(
                observedDescriptors(draft),
                observedDescriptors(native),
                `state step=${step} key=${key}`,
              )
            }
            return draft
          })
          assert.deepEqual(observedDescriptors(current), before)
          assert.deepEqual(observedDescriptors(base), before)
          return 30
        })
      }
      assert.equal(operations, 90_000)
      for (const index of [undefined, 0, 1]) {
        const base = [1, 2, 3]
        if (index !== undefined) Object.defineProperty(base, index, { configurable: false })
        const copy = physicalCopy(base)
        const native = wrapped ? reactive(copy) : copy
        const current = wrapped ? reactive(base) : base
        const before = observedDescriptors(base)
        let actualReads = 0
        let expectedReads = 0
        const expected = operationOutcome(() =>
          Reflect.set(native, 'length', {
            valueOf() {
              expectedReads += 1
              Reflect.set(native, '3', 4)
              return 0
            },
          }),
        )
        produce(current, (draft) => {
          const actual = operationOutcome(() =>
            Reflect.set(draft, 'length', {
              valueOf() {
                actualReads += 1
                draft[3] = 4
                return 0
              },
            }),
          )
          assert.deepEqual(actual, expected)
          assert.equal(actualReads, expectedReads)
          assert.equal(actualReads, 2)
          assert.deepEqual(observedDescriptors(draft), observedDescriptors(native))
          return draft
        })
        assert.deepEqual(observedDescriptors(current), before)
        assert.deepEqual(observedDescriptors(base), before)
      }
    },
    60_000,
  )

  it('matches 10,978 native minimum-deletion and fixed-property feasibility cases', () => {
    let cases = 0
    for (const universe of [
      ['a', 'b', 'c'],
      ['2', 'a', Symbol('s'), Symbol('t')],
    ]) {
      const all = keySequences(universe)
      for (const before of all)
        for (const after of all) cases += checkDeletionOrders(universe, before, after)
    }
    assert.equal(cases, 10_978)
  }, 60_000)

  it.each([false, true])(
    'handles 140,000 distinct parents without an argument-limit failure (undo: %s)',
    (undo) => {
      const shared = { value: 0 }
      const width = 140_000
      const current = {
        parents: Array.from({ length: width }, () => ({ child: shared })),
        wrapped: reactive(shared),
      }
      const next = produce(current, (draft) => {
        draft.parents[0].child.value = 1
        if (undo) draft.parents[0].child.value = 0
        return draft
      })
      assert.equal(next.parents.length, width)
      assert.equal(current.parents[0].child, shared)
      assert.equal(shared.value, 0)
      for (let index = 0; index < width; index += 1) {
        assert.equal(next.parents[index].child, next.parents[0].child)
        assert.equal(next.parents[index] === current.parents[index], undo)
      }
      assert.equal(next.wrapped === current.wrapped, !undo)
      assert.equal(next.parents[0].child.value, undo ? 0 : 1)
      // An undone graph keeps all compatible parents and replaces the wrapper;
      // a changed child instead rejects all those parent proposals.
      const replacement = undo ? next.wrapped : next.parents[0].child
      replacement.value = 7
      assert.equal(shared.value, 0)
      assert.equal(undo ? next.parents[0].child.value : next.wrapped.value, 0)
    },
    60_000,
  )
})

// Checks every fixed-property mask and extensibility for one before/after key order and
// returns the number of cases checked.
function checkDeletionOrders(
  universe: PropertyKey[],
  before: PropertyKey[],
  after: PropertyKey[],
): number {
  let cases = 0
  const desired = orderedObject(after)
  const wanted = Reflect.ownKeys(desired)
  const constraintCount = universe.length === 3 ? 1 << before.length : 1
  for (let fixed = 0; fixed < constraintCount; fixed += 1)
    for (const extensible of [false, true]) {
      checkCase({ after: after.map(String), before: before.map(String), extensible, fixed }, () => {
        checkMinimumDeletions(before, desired, wanted, fixed, extensible)
      })
      cases += 1
    }
  return cases
}

function checkMinimumDeletions(
  before: PropertyKey[],
  desired: object,
  wanted: PropertyKey[],
  fixed: number,
  extensible: boolean,
): void {
  let minDeletes = Number.POSITIVE_INFINITY
  for (let retained = 0; retained < 1 << before.length; retained += 1)
    minDeletes = Math.min(minDeletes, feasibleDeletes(before, wanted, fixed, extensible, retained))
  const base = orderedObject(before, fixed, extensible)
  let deletes = 0
  const current = new Proxy(base, {
    deleteProperty(target, key) {
      deletes += 1
      return Reflect.deleteProperty(target, key)
    },
  })
  if (minDeletes === Number.POSITIVE_INFINITY)
    assert.throws(() => reconcile(current, desired), ReconcileError)
  else {
    assert.equal(reconcile(current, desired), current)
    assert.deepEqual(Reflect.ownKeys(base), wanted)
    assert.equal(deletes, minDeletes)
  }
}

// Native oracle: deletes the keys outside `retained`, then assigns the wanted keys in
// order. Returns the deletion count when that yields exactly the wanted key order, and
// infinity otherwise.
function feasibleDeletes(
  before: PropertyKey[],
  wanted: PropertyKey[],
  fixed: number,
  extensible: boolean,
  retained: number,
): number {
  const candidate = orderedObject(before, fixed, extensible)
  let valid = true
  let deletes = 0
  before.forEach((key, index) => {
    if ((retained & (1 << index)) === 0) {
      valid = Reflect.deleteProperty(candidate, key) && valid
      deletes += 1
    }
  })
  for (const key of wanted) valid = Reflect.set(candidate, key, 0) && valid
  const keys = Reflect.ownKeys(candidate)
  return valid && keys.length === wanted.length && keys.every((key, index) => key === wanted[index])
    ? deletes
    : Number.POSITIVE_INFINITY
}
