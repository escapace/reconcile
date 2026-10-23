import { decodeFail } from './common'
import { builtinValue } from '../standard-prototypes'
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
  return bytes.buffer
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
  if (nativeDecoder === undefined && atobDecoder === undefined) {
    // Without a native decoder: canonical alphabet, and padding only at the end.
    if (/[^A-Z0-9+/=]/i.exec(text) !== null) decodeFail('base64')
    const first = text.indexOf('=')
    if (first !== (end === text.length ? -1 : end)) decodeFail('base64')
  }
  return (text.length / 4) * 3 - (text.length - end)
}
export function encodeBytes(buffer: ArrayBuffer): string {
  const bytes = new Uint8Array(buffer)
  if (nativeEncoder !== undefined) return nativeEncoder.call(bytes)
  if (bytes.length >= tableBytes && typeof TextDecoder === 'function') return encodeTable(bytes)
  let binary = ''
  // apply reads the chunk by index rather than through the iterator protocol; fixed-size
  // chunks keep each call within argument limits and preserve the byte order.
  for (let index = 0; index < bytes.length; index += 0x80_00)
    binary += String.fromCharCode.apply(
      null,
      bytes.subarray(index, index + 0x80_00) as unknown as number[],
    )
  return btoa(binary)
}
function decodeAtob(text: string, length: number): string {
  let binary
  // Always decode, including predicted zero: exact length rules out whitespace.
  try {
    binary = atobDecoder!.call(globalThis, text)
  } catch (error) {
    if (
      typeof DOMException === 'function' &&
      error instanceof DOMException &&
      error.name === 'InvalidCharacterError'
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
    bytes = nativeDecoder!.call(Uint8Array, text, {
      alphabet: 'base64',
      lastChunkHandling: 'loose',
    })
  } catch (error) {
    if (error instanceof SyntaxError) decodeFail('base64')
    throw error
  }
  return dedicatedBuffer(bytes, length)
}
function dedicatedBuffer(bytes: Uint8Array<ArrayBuffer>, length: number): ArrayBuffer {
  if (bytes.byteLength !== length) decodeFail('base64 size')
  if (length !== 0 && hasDedicatedStorage(bytes)) return bytes.buffer
  return bytes.buffer.slice(bytes.byteOffset, bytes.byteOffset + bytes.byteLength)
}

function hasDedicatedStorage(bytes: Uint8Array): boolean {
  return bytes.byteOffset === 0 && bytes.byteLength === bytes.buffer.byteLength
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
function encodeTable(bytes: Uint8Array): string {
  const length = bytes.length
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
