import { decodeFail } from './common'
// v5 native/atob combined validation/decoding. Stable same-realm intrinsics.
// decodedSize is only a prediction on native/atob paths; decodeBytes MUST follow,
// even for length zero. The caller checks structural bounds before native allocation.
// No Node Buffer branch; portable native/atob backends only. No persistent data cache.

const nativeDecoder = /* @__PURE__ */ (() => {
  // eslint-disable-next-line typescript/unbound-method -- The decoder is called with Uint8Array as receiver.
  const decoder = Uint8Array.fromBase64
  return typeof decoder === 'function' ? decoder : undefined
})()
const atobDecoder = /* @__PURE__ */ (() =>
  typeof globalThis.atob === 'function' ? globalThis.atob : undefined)()
export function decodeBytes(text: string, length: number): ArrayBuffer {
  if (nativeDecoder !== undefined) return decodeNativeBytes(text, length)
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
  const bytes = new Uint8Array(length)
  for (let index = 0; index < length; index++) bytes[index] = binary.charCodeAt(index)
  return bytes.buffer
}
export function decodedSize(text: unknown): number {
  if (typeof text !== 'string' || text.length % 4 !== 0) decodeFail('base64')
  // NativeBase64Count.lean: output <= predicted bytes, and exact output
  // forces no ignored whitespace. Other lexical failures are native errors.
  let end = text.length
  if (text.charCodeAt(end - 1) === 61) {
    end--
    if (text.charCodeAt(end - 1) === 61) end--
  }
  if (nativeDecoder === undefined && atobDecoder === undefined) {
    // Base64Full.lean full_gated_language: unchanged fallback rejection policy.
    if (/[^A-Z0-9+/=]/i.exec(text) !== null) decodeFail('base64')
    const first = text.indexOf('=')
    if (first !== (end === text.length ? -1 : end)) decodeFail('base64')
  }
  return (text.length / 4) * 3 - (text.length - end)
}
export function encodeBytes(buffer: ArrayBuffer): string {
  const bytes = new Uint8Array(buffer)
  // eslint-disable-next-line baseline-js/use-baseline -- Capability checked; btoa is the portable fallback.
  if (typeof bytes.toBase64 === 'function') return bytes.toBase64()
  let binary = ''
  // apply uses array-like index reads rather than the spread iterator protocol.
  // Both still need call arguments; no allocation reduction is assumed. Fixed
  // finite chunks retain the same byte order.
  for (let index = 0; index < bytes.length; index += 0x80_00)
    binary += String.fromCharCode.apply(
      null,
      bytes.subarray(index, index + 0x80_00) as unknown as number[],
    )
  return btoa(binary)
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
