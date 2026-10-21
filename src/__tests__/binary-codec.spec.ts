import { assert, it } from 'vitest'
import { encodeBytes } from '../serialization/binary'
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
    assert.equal(encodeBytes(bytes.buffer), reference(bytes), `length ${length}`)
  }
  const all = new Uint8Array(3072)
  for (let index = 0; index < all.length; index++) all[index] = index % 256
  assert.equal(encodeBytes(all.buffer), reference(all))
  assert.equal(
    encodeBytes(new Uint8Array(1024).fill(255).buffer),
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
