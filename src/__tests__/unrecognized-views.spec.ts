// A view over a buffer this environment does not recognize is not recognized either: every
// function handles it as a class instance, whichever of the view and its buffer comes first.
import { runInNewContext } from 'node:vm'
import { expect, it } from 'vitest'
import {
  deserialize,
  isReconcileErrorOfType,
  produce,
  reconcile,
  serialize,
  snapshot,
} from '../index'

/** A view over a buffer whose prototype was replaced, and one from another environment. */
const views = (): Uint8Array[] => {
  const replaced = new Uint8Array([1, 2])
  Object.setPrototypeOf(replaced.buffer, null)
  return [replaced, runInNewContext('new Uint8Array([3, 4])') as Uint8Array]
}

/** A class instance copy of a two-element view: its elements as own data properties. */
const expectInstanceCopy = (copy: unknown, view: Uint8Array): void => {
  expect(ArrayBuffer.isView(copy)).toBe(false)
  expect(Object.getPrototypeOf(copy)).toBe(Object.getPrototypeOf(view))
  expect(Object.getOwnPropertyNames(copy)).toEqual(['0', '1'])
  expect([(copy as Uint8Array)[0], (copy as Uint8Array)[1]]).toEqual([view[0], view[1]])
}

it('copies such a view as a class instance whether its buffer comes first or not', () => {
  for (const view of views()) {
    const [, after] = snapshot([view.buffer, view]) as unknown[]
    const [before] = snapshot([view, view.buffer]) as unknown[]
    expectInstanceCopy(after, view)
    expectInstanceCopy(before, view)
  }
})

it('lets reconcile and produce place such a view as a class instance', () => {
  for (const view of views()) {
    expectInstanceCopy((reconcile({}, { view }) as { view: unknown }).view, view)
    const next = produce({ view }, (draft) => {
      draft.view[0] = 9
      return draft
    })
    expect(ArrayBuffer.isView(next.view)).toBe(false)
    expect(next.view[0]).toBe(9)
  }
})

it('rejects in serialize a view over a buffer without the standard prototype', () => {
  for (const prototype of [null, Object.prototype]) {
    const view = new Uint8Array(2)
    Object.setPrototypeOf(view.buffer, prototype)
    for (const value of [view, [view.buffer, view]]) {
      let thrown: unknown
      try {
        serialize(value)
      } catch (error) {
        thrown = error
      }
      expect(isReconcileErrorOfType(thrown as never, 'SerializeValueUnsupported')).toBe(true)
    }
  }
})

/** Views whose own prototype was replaced, and a `DataView` that inherits a typed array's. */
const replacedViews = (): object[] => [
  Object.setPrototypeOf(new DataView(new ArrayBuffer(2)), null) as object,
  Object.setPrototypeOf(new DataView(new ArrayBuffer(2)), Object.prototype) as object,
  Object.setPrototypeOf(new Uint8Array([5, 6]), null) as object,
  Object.setPrototypeOf(new DataView(new ArrayBuffer(2)), Uint8Array.prototype) as object,
]

/** A copy made through the own properties alone: same prototype, no view brand. */
const expectOwnPropertyCopy = (copy: unknown, view: object): void => {
  expect(ArrayBuffer.isView(copy)).toBe(false)
  expect(Object.getPrototypeOf(copy)).toBe(Object.getPrototypeOf(view))
  expect(Reflect.ownKeys(copy as object)).toEqual(Reflect.ownKeys(view))
}

it('handles a view whose own prototype was replaced through its own properties', () => {
  for (const view of replacedViews()) {
    expectOwnPropertyCopy(snapshot(view), view)
    expectOwnPropertyCopy((reconcile({}, { view }) as { view: unknown }).view, view)
    const next = produce({ view }, (draft) => {
      Reflect.set(draft.view, 'label', 1)
      return draft
    })
    expect(ArrayBuffer.isView(next.view)).toBe(false)
    expect(Reflect.get(next.view, 'label')).toBe(1)
  }
})

/** A typed array whose prototype was set to `DataView.prototype`: a `DataView` by its chain. */
const typedDataView = (): DataView =>
  Object.setPrototypeOf(new Uint8Array([1, 2, 3, 4]).subarray(1), DataView.prototype) as DataView

/** The `DataView` getter `name` of `view`, read past any prototype. */
const readDataView = (view: unknown, name: string): unknown =>
  Object.getOwnPropertyDescriptor(DataView.prototype, name)!.get!.call(view)

/** A `DataView` over a copy of the bytes, with the source's offset and length, whose first byte
 * in view is `first`. */
const expectDataViewCopy = (copy: unknown, first: number): void => {
  expect(Object.getPrototypeOf(copy)).toBe(DataView.prototype)
  expect(readDataView(copy, 'byteOffset')).toBe(1)
  expect(readDataView(copy, 'byteLength')).toBe(3)
  expect([...new Uint8Array(readDataView(copy, 'buffer') as ArrayBuffer)]).toEqual([1, first, 3, 4])
}

it('copies a typed array that inherits DataView.prototype as a DataView over its own bytes', () => {
  // The chain decides the kind, and the copy takes the value's own offset and length.
  expectDataViewCopy(snapshot(typedDataView()), 2)
  expectDataViewCopy((reconcile({}, { view: typedDataView() }) as { view: unknown }).view, 2)
  const next = produce({ view: typedDataView() }, (draft) => {
    draft.view.setUint8(0, 9)
    return draft
  })
  expectDataViewCopy(next.view, 9)
})

it('serializes a typed array that inherits DataView.prototype as the DataView the others copy', () => {
  expectDataViewCopy(deserialize(serialize(typedDataView()), { maxBytes: Infinity }), 2)
})

it("rejects in serialize a typed array given another element type's prototype", () => {
  // deserialize builds the element type the prototype names, which would read other bytes.
  for (const view of [
    Object.setPrototypeOf(new Uint16Array([1, 2]), Uint8Array.prototype) as object,
    Object.setPrototypeOf(new Uint8Array([1, 2, 3, 4]), Uint16Array.prototype) as object,
  ]) {
    let thrown: unknown
    try {
      serialize(view)
    } catch (error) {
      thrown = error
    }
    expect(thrown).toBeDefined()
    expect(isReconcileErrorOfType(thrown as never, 'SerializeValueUnsupported')).toBe(true)
  }
})
