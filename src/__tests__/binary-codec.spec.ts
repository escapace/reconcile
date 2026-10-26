import { assert, it } from 'vitest'
import { decodeBytes, decodedSize, encodeBytes } from '../serialization/binary'
import { decodeText, encodeText } from './fixtures/text-codec'

// The reference encoder: the binary string of the bytes through the platform's btoa.
function reference(bytes: Uint8Array): string {
  let binary = ''
  for (const byte of bytes) binary += String.fromCharCode(byte)
  return btoa(binary)
}
function sample(length: number, seed: number): Uint8Array<ArrayBuffer> {
  const bytes = new Uint8Array(length)
  for (let index = 0; index < length; index++)
    bytes[index] = (Math.imul(index + seed, 2_654_435_761) >>> 24) & 255
  return bytes
}

// Base64.lean encode_spec: the table encoder used for longer buffers writes the bytes btoa writes.
it('encodes every length across the encoder threshold as btoa does', () => {
  for (let length = 0; length <= 2100; length++) {
    const bytes = sample(length, length)
    assert.equal(encodeBytes(bytes.buffer, length), reference(bytes), `length ${length}`)
  }
  const all = new Uint8Array(3072)
  for (let index = 0; index < all.length; index++) all[index] = index % 256
  assert.equal(encodeBytes(all.buffer, all.length), reference(all))
  assert.equal(
    encodeBytes(new Uint8Array(1024).fill(255).buffer, 1024),
    reference(new Uint8Array(1024).fill(255)),
  )
})

it('round-trips buffers on both sides of the encoder threshold', () => {
  for (const length of [0, 1, 2, 3, 1023, 1024, 1025, 1026, 4099]) {
    const bytes = sample(length, 7)
    const copy = decodeText(encodeText(bytes.buffer)) as ArrayBuffer
    assert.deepEqual(new Uint8Array(copy), bytes, `length ${length}`)
  }
})

// Base64.lean decode_encode: the table decoder used for longer buffers returns the encoded bytes,
// in a fixed-length buffer of exactly their length.
it('decodes every length across the decoder threshold to the encoded bytes', () => {
  for (let length = 1000; length <= 1100; length++) {
    const bytes = sample(length, length)
    const text = encodeBytes(bytes.buffer, length)
    const decoded = decodeBytes(text, decodedSize(text))
    assert.equal(Object.getPrototypeOf(decoded), ArrayBuffer.prototype)
    // eslint-disable-next-line baseline-js/use-baseline -- the engines the tests run on have it
    assert.equal(decoded.resizable, false)
    assert.deepEqual(new Uint8Array(decoded), bytes, `length ${length}`)
  }
})

// An outcome as text: the bytes in hex, or the detail of the format error.
function outcome(decode: () => Uint8Array): string {
  try {
    let hex = ''
    for (const byte of decode()) hex += byte.toString(16).padStart(2, '0')
    return hex
  } catch (error) {
    if (error instanceof DOMException) return 'base64'
    const message = (error as Error).message
    return message.endsWith('base64 size.')
      ? 'base64 size'
      : message.endsWith('base64.')
        ? 'base64'
        : message
  }
}
// The atob path the table decoder replaces for longer buffers.
function atobBytes(text: string): Uint8Array {
  const length = decodedSize(text)
  const binary = atob(text)
  if (binary.length !== length) throw new Error('base64 size.')
  const bytes = new Uint8Array(length)
  for (let index = 0; index < length; index++) bytes[index] = binary.charCodeAt(index)
  return bytes
}

// A code outside the alphabet sends the text to the atob path, so a longer buffer's text decodes,
// or fails, as atob decides: whitespace, a misplaced pad, non-ASCII and changed padding included.
it('decodes or rejects longer corrupted text as the atob path does', () => {
  const marks = [' ', '\n', '\t', '=', '*', '-', '_', 'é', '\u{1F600}', '\u0000', 'A']
  for (let index = 0; index < 600; index++) {
    const length = 1024 + ((index * 37) % 200)
    const text = encodeBytes(sample(length, index).buffer, length)
    const at = (index * 7919) % text.length
    const mark = marks[index % marks.length]
    const corrupted =
      index % 5 === 0 ? `${text.slice(0, -1)}=` : text.slice(0, at) + mark + text.slice(at + 1)
    assert.equal(
      outcome(() => new Uint8Array(decodeBytes(corrupted, decodedSize(corrupted)))),
      outcome(() => atobBytes(corrupted)),
      `case ${index}`,
    )
  }
})
