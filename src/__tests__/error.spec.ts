import { assert, describe, expectTypeOf, it } from 'vitest'
import {
  isReconcileError,
  isReconcileErrorOfType,
  produce,
  RECONCILE_ERROR_TYPES,
  reconcile,
  ReconcileError,
} from '../index'
import type { ReconcileErrorMetadata, ReconcileErrorType } from '../index'

function thrown(run: () => unknown): unknown {
  try {
    run()
  } catch (error) {
    return error
  }
  assert.fail('expected a throw')
}

describe('ReconcileError', () => {
  it('lists every type exactly once, sorted, and matches the metadata keys', () => {
    assert.deepEqual([...RECONCILE_ERROR_TYPES], [...new Set(RECONCILE_ERROR_TYPES)].sort())
    expectTypeOf<keyof ReconcileErrorMetadata>().toEqualTypeOf<ReconcileErrorType>()
    for (const type of RECONCILE_ERROR_TYPES)
      assert.match(type, /^(?:Deserialize|Draft|Finalization|Publication|Serialize|Snapshot)[A-Z]/)
  })

  it('is a plain Error with a stable name and a discriminated cause', () => {
    const error = thrown(() => reconcile({}, []))
    assert.instanceOf(error, Error)
    assert.equal(error.message, 'reconcile cannot make current match next.')
    assert.instanceOf(error, ReconcileError)
    assert.ok(isReconcileError(error))
    assert.equal(error.name, 'ReconcileError')
    assert.deepEqual(error.cause, { type: 'PublicationRejected' })
    assert.ok(isReconcileErrorOfType(error, 'PublicationRejected'))
    assert.notOk(isReconcileErrorOfType(error, 'DraftDefinePropertyUnsupported'))
    assert.notInstanceOf(error, TypeError)
  })

  it('reports the property of a rejected reflective definition', () => {
    const error = thrown(() =>
      produce({ a: 1 }, (draft) => {
        Object.defineProperty(draft, 'b', { value: 2 })
        return draft
      }),
    )
    assert.ok(isReconcileError(error))
    assert.deepEqual(error.cause, { property: 'b', type: 'DraftDefinePropertyUnsupported' })
  })

  it('reports an accessor met after observations were sealed with its property', () => {
    const current = { child: { value: 0 }, flag: 0 }
    Object.defineProperty(current, 'replace', {
      configurable: true,
      enumerable: true,
      get(this: typeof current) {
        this.child = {
          get value() {
            return 2
          },
        }
        return 1
      },
    })
    const error = thrown(() =>
      produce(current, (draft) => {
        draft.flag = 1
        return draft
      }),
    )
    assert.ok(isReconcileError(error))
    assert.deepEqual(error.cause, { property: 'value', type: 'FinalizationAccessorUnstable' })
  })

  it('keeps native RangeError semantics for invalid array lengths', () => {
    const error = thrown(() =>
      produce([1, 2], (draft) => {
        draft.length = -1
        return draft
      }),
    )
    assert.instanceOf(error, RangeError)
    assert.notOk(isReconcileError(error))
  })

  it('propagates application exceptions unchanged', () => {
    const boom = new Error('boom')
    const error = thrown(() =>
      produce(
        {
          get value(): number {
            throw boom
          },
        },
        (draft) => draft.value,
      ),
    )
    assert.equal(error, boom)
  })
})
