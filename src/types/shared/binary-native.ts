import { freeze } from './empty'
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

/** `%TypedArray%` as `inChain` reads it: the class every built-in typed array class extends. */
export const typedArrayClass = /* @__PURE__ */ (() => freeze({ prototype: typedPrototype }))()

export const getter = (
  prototype: object,
  key: PropertyKey,
): ((this: object) => unknown) | undefined =>
  // eslint-disable-next-line typescript/unbound-method -- Native accessors are always invoked with an explicit receiver.
  Object.getOwnPropertyDescriptor(prototype, key)?.get

// A built-in getter, read when the module loads and called on its receiver without an argument
// list.
const getterOf = <Result>(
  prototype: object,
  key: PropertyKey,
): ((target: object) => Result) | undefined => {
  const get = getter(prototype, key)
  return get === undefined ? undefined : uncurried<[], Result>(get)
}
const bufferLengthOf = /* @__PURE__ */ (() =>
  getterOf<number>(ArrayBuffer.prototype, 'byteLength')!)()
const sharedLengthOf = /* @__PURE__ */ (() =>
  typeof SharedArrayBuffer === 'function'
    ? getterOf<number>(SharedArrayBuffer.prototype as object, 'byteLength')
    : undefined)()
const resizableOf = /* @__PURE__ */ (() => getterOf<boolean>(ArrayBuffer.prototype, 'resizable'))()
const maxLengthOf = /* @__PURE__ */ (() =>
  getterOf<number>(ArrayBuffer.prototype, 'maxByteLength'))()
const typedNameOf = /* @__PURE__ */ (() =>
  getterOf<string | undefined>(typedPrototype, Symbol.toStringTag)!)()
export const typedBufferOf = /* @__PURE__ */ (() =>
  getterOf<ArrayBuffer>(typedPrototype, 'buffer')!)()
export const typedOffsetOf = /* @__PURE__ */ (() =>
  getterOf<number>(typedPrototype, 'byteOffset')!)()
export const typedLengthOf = /* @__PURE__ */ (() => getterOf<number>(typedPrototype, 'length')!)()
export const typedByteLengthOf = /* @__PURE__ */ (() =>
  getterOf<number>(typedPrototype, 'byteLength')!)()
export const dataBufferOf = /* @__PURE__ */ (() =>
  getterOf<ArrayBuffer>(DataView.prototype, 'buffer')!)()
export const dataOffsetOf = /* @__PURE__ */ (() =>
  getterOf<number>(DataView.prototype, 'byteOffset')!)()
export const dataLengthOf = /* @__PURE__ */ (() =>
  getterOf<number>(DataView.prototype, 'byteLength')!)()

/** Whether a buffer whose prototype is `prototype` is a `SharedArrayBuffer`. */
const sharedOn = (prototype: object | null): boolean =>
  sharedLengthOf !== undefined && inChain(prototype, SharedArrayBuffer)

/** Whether a buffer is a `SharedArrayBuffer`, which every function keeps by reference. */
export const isShared = (buffer: object): boolean =>
  sharedOn(Object.getPrototypeOf(buffer) as object | null)

/** Whether a buffer is resizable. */
export const isResizable = (buffer: object): boolean => resizableOf?.(buffer) === true

/** A buffer's length in bytes. */
export const bufferByteLength = (buffer: object): number =>
  isShared(buffer) ? sharedLengthOf!(buffer) : bufferLengthOf(buffer)

/** The length a resizable buffer can grow to, or -1 for a fixed-length or shared buffer. */
export const bufferMaximum = (buffer: object): number =>
  isShared(buffer) || !isResizable(buffer) ? -1 : maxLengthOf!(buffer)

// The built-in `set` of typed arrays, read when the module loads.
const typedSet = /* @__PURE__ */ (() =>
  uncurried<[source: ArrayBufferView, offset?: number], undefined>(
    builtinValue(typedPrototype, 'set'),
  ))()

/** Copies the bytes of `source` to the start of `target`, which holds at least as many, with the
 * built-in `set`. */
const copyBytes = (target: ArrayBufferLike, source: ArrayBufferLike): void => {
  typedSet(new Uint8Array(target), new Uint8Array(source))
}

/** Copies the bytes of `source` into `target`, of the same length, when any differs, with the
 * built-in `set`; returns whether it wrote. */
export function copyChangedBytes(target: ArrayBufferLike, source: ArrayBufferLike): boolean {
  const left = new Uint8Array(target)
  const right = new Uint8Array(source)
  const length = typedLengthOf(right)
  for (let index = 0; index < length; index += 1)
    if (left[index] !== right[index]) {
      typedSet(left, right)
      return true
    }
  return false
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
 * maximum. A `SharedArrayBuffer` is its own copy, so a view copied over it shares its memory. The
 * prototype is read once, or passed by a caller that read it (Types.Ingress.bufferCopy_once).
 */
export function copyBuffer(
  buffer: object,
  prototype = Object.getPrototypeOf(buffer) as object | null,
): ArrayBuffer {
  if (sharedOn(prototype)) return buffer as ArrayBuffer
  const copy = emptyBuffer(buffer, bufferLengthOf(buffer))
  copyBytes(copy, buffer as ArrayBuffer)
  return adoptPrototype(copy, prototype, ArrayBuffer.prototype)
}

/** A new zero-filled buffer of `length` bytes, resizable to the same maximum as `buffer` is. */
function emptyBuffer(buffer: object, length: number): ArrayBuffer {
  if (!isResizable(buffer)) return new ArrayBuffer(length)
  const maxByteLength = maxLengthOf!(buffer)
  // eslint-disable-next-line baseline-js/use-baseline -- reached only where the engine has resizable buffers
  return new ArrayBuffer(length, { maxByteLength })
}

/** A typed array's element type, such as `'Uint8Array'`, or `undefined` for a `DataView`. */
export const viewElement = (view: object): string | undefined => typedNameOf(view)

/** The buffer of a view whose element type `element` was read, through the getter it selects. */
export const bufferWith = (view: object, element: string | undefined): ArrayBuffer =>
  element === undefined ? dataBufferOf(view) : typedBufferOf(view)

/** A view's backing buffer. */
export const bufferOfView = (view: object): ArrayBuffer => bufferWith(view, viewElement(view))

/** A view's offset in its buffer, in bytes. */
export const viewOffset = (view: object): number =>
  viewElement(view) === undefined ? dataOffsetOf(view) : typedOffsetOf(view)

/** A view's length in bytes. */
export const viewByteLength = (view: object): number =>
  viewElement(view) === undefined ? dataLengthOf(view) : typedByteLengthOf(view)

/** The names of `viewConstructors`, read once. */
export const viewNames: readonly string[] = /* @__PURE__ */ (() =>
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
export function copyTypedArray(
  value: object,
  buffer: ArrayBuffer,
  prototype = Object.getPrototypeOf(value) as object | null,
  element = viewElement(value),
): ArrayBufferView {
  const Constructor = elementConstructor(element!)
  return adoptPrototype(
    new Constructor(buffer, typedOffsetOf(value), typedLengthOf(value)),
    prototype,
    Constructor.prototype,
  )
}

/** A `DataView` with the source's offset and length over `buffer`, on the source's prototype. */
export function copyDataView(
  value: object,
  buffer: ArrayBuffer,
  prototype = Object.getPrototypeOf(value) as object | null,
  element = viewElement(value),
): DataView {
  const typed = element !== undefined
  return adoptPrototype(
    new DataView(
      buffer,
      typed ? typedOffsetOf(value) : dataOffsetOf(value),
      typed ? typedByteLengthOf(value) : dataLengthOf(value),
    ),
    prototype,
    DataView.prototype,
  )
}
