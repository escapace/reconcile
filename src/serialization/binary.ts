import { decodeFail } from './common'
import { builtinValue } from '../standard-prototypes'
import { inChain } from '../object-property'
import {
  bufferByteLength,
  bufferOfView,
  sliceBytes,
  viewByteLength,
  viewOffset,
} from '../types/shared/binary-native'
// Base64 decoding through the stable same-realm native decoder or atob, validated together.
// decodedSize is only a prediction on those paths; decodeBytes or checkBytes MUST follow, even
// for length zero. The caller checks structural bounds before native allocation. No Node Buffer
// branch and no persistent data cache.

// Both native codecs are read as own properties when the module loads, so a method that
// Object.prototype holds is never taken for one the engine lacks.
const nativeDecoder = /* @__PURE__ */ (() => {
  const decoder = builtinValue(Uint8Array, 'fromBase64')
  return typeof decoder === 'function'
    ? (decoder as (
        text: string,
        options: { alphabet: string; lastChunkHandling: string },
      ) => Uint8Array<ArrayBuffer>)
    : undefined
})()
const nativeEncoder = /* @__PURE__ */ (() => {
  const encoder = builtinValue(Uint8Array.prototype, 'toBase64')
  return typeof encoder === 'function' ? (encoder as (this: Uint8Array) => string) : undefined
})()
const atobDecoder = /* @__PURE__ */ (() =>
  typeof globalThis.atob === 'function' ? globalThis.atob : undefined)()
export function decodeBytes(text: string, length: number): ArrayBuffer {
  if (nativeDecoder !== undefined) return decodeNativeBytes(text, length)
  const binary = decodeAtob(text, length)
  const bytes = new Uint8Array(length)
  for (let index = 0; index < length; index++) bytes[index] = binary.charCodeAt(index)
  return bufferOfView(bytes)
}
// For measuring, which reads only the byte length: the same checks as decodeBytes, without
// copying the bytes atob returns.
export function checkBytes(text: string, length: number): ArrayBuffer {
  if (nativeDecoder !== undefined) return decodeNativeBytes(text, length)
  decodeAtob(text, length)
  return new ArrayBuffer(length)
}
export function decodedSize(text: unknown): number {
  if (typeof text !== 'string' || text.length % 4 !== 0) decodeFail('base64')
  // Runtime obligation (serialization-boundaries.spec.ts): a native decoder never yields more
  // bytes than predicted, so requiring the exact count also rejects ignored whitespace. Other
  // lexical failures are native errors.
  let end = text.length
  if (text.charCodeAt(end - 1) === 61) {
    end--
    if (text.charCodeAt(end - 1) === 61) end--
  }
  return (text.length / 4) * 3 - (text.length - end)
}
/** The base64 text of the `length` bytes of `buffer`. */
export function encodeBytes(buffer: ArrayBuffer, length: number): string {
  const bytes = new Uint8Array(buffer)
  if (nativeEncoder !== undefined) return Reflect.apply(nativeEncoder, bytes, [])
  if (length >= tableBytes && typeof TextDecoder === 'function') return encodeTable(bytes, length)
  // apply reads the chunk by index rather than through the iterator protocol; fixed-size
  // chunks keep each call within argument limits and preserve the byte order. One chunk is the
  // whole buffer.
  if (length <= 0x80_00) return btoa(String.fromCharCode.apply(null, bytes as unknown as number[]))
  let binary = ''
  for (let index = 0; index < length; index += 0x80_00)
    binary += String.fromCharCode.apply(
      null,
      new Uint8Array(buffer, index, Math.min(0x80_00, length - index)) as unknown as number[],
    )
  return btoa(binary)
}
// Whether a native decoder threw an error of `constructor`'s class, decided by the prototype chain
// so that an overridden `Symbol.hasInstance` does not decide it.
const nativeError = (error: unknown, constructor: { readonly prototype: unknown }): boolean =>
  typeof error === 'object' &&
  error !== null &&
  inChain(Object.getPrototypeOf(error) as object | null, constructor)

function decodeAtob(text: string, length: number): string {
  let binary
  // Always decode, including predicted zero: exact length rules out whitespace.
  try {
    binary = Reflect.apply(atobDecoder!, globalThis, [text])
  } catch (error) {
    if (
      typeof DOMException === 'function' &&
      nativeError(error, DOMException) &&
      (error as DOMException).name === 'InvalidCharacterError'
    )
      decodeFail('base64')
    throw error
  }
  if (binary.length !== length) decodeFail('base64 size')
  return binary
}
function decodeNativeBytes(text: string, length: number): ArrayBuffer {
  let bytes
  try {
    bytes = Reflect.apply(nativeDecoder!, Uint8Array, [
      text,
      { alphabet: 'base64', lastChunkHandling: 'loose' },
    ])
  } catch (error) {
    if (nativeError(error, SyntaxError)) decodeFail('base64')
    throw error
  }
  return dedicatedBuffer(bytes, length)
}
// The decoder's bytes, read with the built-in accessors: their own buffer when they fill it,
// otherwise a copy of them.
function dedicatedBuffer(bytes: Uint8Array<ArrayBuffer>, length: number): ArrayBuffer {
  if (viewByteLength(bytes) !== length) decodeFail('base64 size')
  const buffer = bufferOfView(bytes)
  const offset = viewOffset(bytes)
  if (length !== 0 && offset === 0 && length === bufferByteLength(buffer)) return buffer
  return sliceBytes(buffer, offset, length)
}
// Below this many bytes, building the binary string for btoa costs less than one TextDecoder
// call; above it, the table encoder avoids the argument copies of String.fromCharCode.apply.
const tableBytes = 1024
// The ASCII codes of the base64 alphabet, indexed by 6-bit value: constant data.
const alphabet = /* @__PURE__ */ (() => {
  const codes = new Uint8Array(64)
  const text = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/'
  for (let index = 0; index < 64; index++) codes[index] = text.charCodeAt(index)
  return codes
})()
// Base64.lean encode_spec: each group of three bytes is one 24-bit word whose four 6-bit fields
// index the alphabet; a final group of two or one bytes keeps three or two fields, then pads.
function encodeTable(bytes: Uint8Array, length: number): string {
  const ascii = new Uint8Array(Math.ceil(length / 3) * 4)
  let out = 0
  let index = 0
  for (; index + 2 < length; index += 3) {
    const word = (bytes[index] << 16) | (bytes[index + 1] << 8) | bytes[index + 2]
    ascii[out++] = alphabet[word >> 18]
    ascii[out++] = alphabet[(word >> 12) & 63]
    ascii[out++] = alphabet[(word >> 6) & 63]
    ascii[out++] = alphabet[word & 63]
  }
  if (index < length) {
    const two = index + 1 < length
    const word = (bytes[index] << 16) | (two ? bytes[index + 1] << 8 : 0)
    ascii[out++] = alphabet[word >> 18]
    ascii[out++] = alphabet[(word >> 12) & 63]
    ascii[out++] = two ? alphabet[(word >> 6) & 63] : 61
    ascii[out] = 61
  }
  return new TextDecoder().decode(ascii)
}
