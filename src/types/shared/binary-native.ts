import { adoptPrototype } from './prototype'
import { inChain } from '../../object-property'
import { builtinValue, uncurried } from '../../standard-prototypes'

/**
 * Buffers and views read and built through the built-in accessors and constructors: a getter or
 * constructor that an instance, a subclass or a patched prototype overrides is never called, as for
 * dates and URLs.
 * @internal
 */

/** A typed-array constructor, as the built-in constructors are called. */
export interface ViewConstructor {
  new (buffer: ArrayBuffer, offset: number, length: number): ArrayBufferView
  readonly BYTES_PER_ELEMENT: number
  readonly prototype: object
}

/** The built-in typed-array constructors; one the global lacks is `undefined`. */
export const viewConstructors: ReadonlyArray<ViewConstructor | undefined> = /* @__PURE__ */ (() =>
  Object.freeze([
    Int8Array,
    Uint8Array,
    Uint8ClampedArray,
    Int16Array,
    Uint16Array,
    Int32Array,
    Uint32Array,
    globalThis.Float16Array,
    Float32Array,
    Float64Array,
    BigInt64Array,
    BigUint64Array,
  ]))()

const typedPrototype = /* @__PURE__ */ (() =>
  Object.getPrototypeOf(Uint8Array.prototype) as object)()

export const getter = (
  prototype: object,
  key: PropertyKey,
): ((this: object) => unknown) | undefined =>
  // eslint-disable-next-line typescript/unbound-method -- Native accessors are always invoked with an explicit receiver.
  Object.getOwnPropertyDescriptor(prototype, key)?.get

const bufferLength = /* @__PURE__ */ (() => getter(ArrayBuffer.prototype, 'byteLength')!)()
const sharedLength = /* @__PURE__ */ (() =>
  typeof SharedArrayBuffer === 'function'
    ? getter(SharedArrayBuffer.prototype as object, 'byteLength')
    : undefined)()
export const bufferResizable = /* @__PURE__ */ (() => getter(ArrayBuffer.prototype, 'resizable'))()
const bufferMaxLength = /* @__PURE__ */ (() => getter(ArrayBuffer.prototype, 'maxByteLength'))()
const typedName = /* @__PURE__ */ (() => getter(typedPrototype, Symbol.toStringTag)!)()
export const typedBuffer = /* @__PURE__ */ (() => getter(typedPrototype, 'buffer')!)()
export const typedOffset = /* @__PURE__ */ (() => getter(typedPrototype, 'byteOffset')!)()
export const typedLength = /* @__PURE__ */ (() => getter(typedPrototype, 'length')!)()
const typedByteLength = /* @__PURE__ */ (() => getter(typedPrototype, 'byteLength')!)()
export const dataBuffer = /* @__PURE__ */ (() => getter(DataView.prototype, 'buffer')!)()
export const dataOffset = /* @__PURE__ */ (() => getter(DataView.prototype, 'byteOffset')!)()
export const dataLength = /* @__PURE__ */ (() => getter(DataView.prototype, 'byteLength')!)()

/** Whether a buffer is a `SharedArrayBuffer`, which every function keeps by reference. */
export const isShared = (buffer: object): boolean =>
  sharedLength !== undefined &&
  inChain(Object.getPrototypeOf(buffer) as object | null, SharedArrayBuffer)

/** A buffer's length in bytes. */
export const bufferByteLength = (buffer: object): number =>
  Reflect.apply(isShared(buffer) ? sharedLength! : bufferLength, buffer, []) as number

// The built-in `set` of typed arrays, read when the module loads.
const typedSet = /* @__PURE__ */ (() =>
  uncurried<[source: ArrayBufferView, offset?: number], undefined>(
    builtinValue(typedPrototype, 'set'),
  ))()

/** Copies the bytes of `source` to the start of `target`, which holds at least as many, with the
 * built-in `set`. */
export const copyBytes = (target: ArrayBufferLike, source: ArrayBufferLike): void => {
  typedSet(new Uint8Array(target), new Uint8Array(source))
}

/** A new buffer holding the `length` bytes of `buffer` from `offset`. */
export function sliceBytes(buffer: ArrayBuffer, offset: number, length: number): ArrayBuffer {
  const copy = new ArrayBuffer(length)
  typedSet(new Uint8Array(copy), new Uint8Array(buffer, offset, length))
  return copy
}

/**
 * A copy of a buffer's bytes on the buffer's prototype, made without calling its constructor, as
 * `slice` would through `Symbol.species`. A resizable buffer's copy is resizable to the same
 * maximum. A `SharedArrayBuffer` is its own copy, so a view copied over it shares its memory.
 */
export function copyBuffer(buffer: object): ArrayBuffer {
  if (isShared(buffer)) return buffer as ArrayBuffer
  const copy = emptyBuffer(buffer, bufferByteLength(buffer))
  copyBytes(copy, buffer as ArrayBuffer)
  return adoptPrototype(copy, Object.getPrototypeOf(buffer) as object | null, ArrayBuffer.prototype)
}

/** A new zero-filled buffer of `length` bytes, resizable to the same maximum as `buffer` is. */
function emptyBuffer(buffer: object, length: number): ArrayBuffer {
  if (bufferResizable === undefined || Reflect.apply(bufferResizable, buffer, []) !== true)
    return new ArrayBuffer(length)
  const maxByteLength = Reflect.apply(bufferMaxLength!, buffer, []) as number
  // eslint-disable-next-line baseline-js/use-baseline -- reached only where the engine has resizable buffers
  return new ArrayBuffer(length, { maxByteLength })
}

/** A typed array's element type, such as `'Uint8Array'`, or `undefined` for a `DataView`. */
export const viewElement = (view: object): string | undefined =>
  Reflect.apply(typedName, view, []) as string | undefined

/** A view's backing buffer. */
export const bufferOfView = (view: object): ArrayBuffer =>
  Reflect.apply(viewElement(view) === undefined ? dataBuffer : typedBuffer, view, []) as ArrayBuffer

/** A view's offset in its buffer, in bytes. */
export const viewOffset = (view: object): number =>
  Reflect.apply(viewElement(view) === undefined ? dataOffset : typedOffset, view, []) as number

/** A view's length in bytes. */
export const viewByteLength = (view: object): number =>
  Reflect.apply(viewElement(view) === undefined ? dataLength : typedByteLength, view, []) as number

/** The names of `viewConstructors`, read once. */
const viewNames: readonly string[] = /* @__PURE__ */ (() =>
  Object.freeze(viewConstructors.map((constructor) => constructor?.name ?? '')))()

/** The built-in constructor of a typed array's element type. */
function elementConstructor(name: string): ViewConstructor {
  for (let index = 0; index < viewNames.length; index += 1)
    if (viewNames[index] === name) return viewConstructors[index]!
  // An element type whose global constructor was removed cannot be built.
  throw new TypeError(`${name} is not available`)
}

/**
 * A typed array with the source's element type, offset and length over `buffer`, on the source's
 * prototype, made with the built-in constructor.
 */
export function copyTypedArray(value: object, buffer: ArrayBuffer): ArrayBufferView {
  const Constructor = elementConstructor(viewElement(value)!)
  return adoptPrototype(
    new Constructor(
      buffer,
      Reflect.apply(typedOffset, value, []) as number,
      Reflect.apply(typedLength, value, []) as number,
    ),
    Object.getPrototypeOf(value) as object | null,
    Constructor.prototype,
  )
}

/** A `DataView` with the source's offset and length over `buffer`, on the source's prototype. */
export function copyDataView(value: object, buffer: ArrayBuffer): DataView {
  return adoptPrototype(
    new DataView(buffer, viewOffset(value), viewByteLength(value)),
    Object.getPrototypeOf(value) as object | null,
    DataView.prototype,
  )
}
