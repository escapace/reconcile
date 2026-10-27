import { afterEach, assert, describe, it, vi } from 'vitest'
import { isReconcileError } from '../index'
import { decodeText, encodeText } from './fixtures/text-codec'
import { thrown } from './fixtures/thrown'

function failure(run: () => unknown): { reason: string; type: string } {
  const error = thrown(run)
  assert.ok(isReconcileError(error))
  return error.cause as { reason: string; type: string }
}

// Stand-ins with the native contract the codec relies on: whitespace is skipped, other
// characters outside the alphabet throw SyntaxError. A decoded result may share a larger
// buffer, which the codec must not expose.
async function loadWithNativeBase64(offset: number) {
  Object.defineProperty(Uint8Array, 'fromBase64', {
    configurable: true,
    value: (input: string) => {
      const stripped = input.replaceAll(/[\t\n\f\r ]/g, '')
      if (/[^\d+/=a-z]/i.test(stripped)) throw new SyntaxError('invalid base64')
      const binary = atob(stripped)
      const backing = new Uint8Array(binary.length + offset)
      for (let index = 0; index < binary.length; index++)
        backing[index + offset] = binary.charCodeAt(index)
      return backing.subarray(offset)
    },
  })
  // eslint-disable-next-line no-extend-native -- a temporary stand-in for a method newer engines ship; removed after each test
  Object.defineProperty(Uint8Array.prototype, 'toBase64', {
    configurable: true,
    value(this: Uint8Array) {
      let binary = ''
      for (const byte of this) binary += String.fromCharCode(byte)
      return btoa(binary)
    },
  })
  vi.resetModules()
  return await import('../index')
}

describe('base64 payloads', () => {
  const text = encodeText(new Uint8Array([1, 2, 3]).buffer)

  it('rejects whitespace, characters outside the alphabet and inner padding', () => {
    assert.ok(text.includes('"AQID"'))
    assert.deepEqual(
      failure(() => decodeText(text.replace('AQID', 'AQ D'))),
      { reason: 'base64 size', type: 'DeserializeInputInvalid' },
    )
    for (const tampered of ['AQI*', 'AQ=D'])
      assert.deepEqual(
        failure(() => decodeText(text.replace('AQID', tampered))),
        {
          reason: 'base64',
          type: 'DeserializeInputInvalid',
        },
      )
  })

  it('classifies a decoder error by its prototype chain, not by Symbol.hasInstance', () => {
    const constructors = [DOMException, SyntaxError]
    for (const constructor of constructors)
      Object.defineProperty(constructor, Symbol.hasInstance, {
        configurable: true,
        value: () => false,
      })
    try {
      assert.deepEqual(
        failure(() => decodeText(text.replace('AQID', 'AQI*'))),
        {
          reason: 'base64',
          type: 'DeserializeInputInvalid',
        },
      )
    } finally {
      for (const constructor of constructors)
        Reflect.deleteProperty(constructor, Symbol.hasInstance)
    }
  })

  describe('through the native Uint8Array base64 methods', () => {
    afterEach(() => {
      Reflect.deleteProperty(Uint8Array, 'fromBase64')
      Reflect.deleteProperty(Uint8Array.prototype, 'toBase64')
      vi.resetModules()
    })

    it('classifies the native SyntaxError by its prototype chain', async () => {
      const api = await loadWithNativeBase64(0)
      const wire = JSON.stringify(api.serialize(new Uint8Array([1, 2, 3]).buffer))
      Object.defineProperty(SyntaxError, Symbol.hasInstance, {
        configurable: true,
        value: () => false,
      })
      let caught: unknown
      try {
        api.deserialize(JSON.parse(wire.replace('AQID', 'AQI*')), { maxBytes: Infinity })
      } catch (error) {
        caught = error
      } finally {
        Reflect.deleteProperty(SyntaxError, Symbol.hasInstance)
      }
      assert.ok(api.isReconcileError(caught))
      assert.deepEqual(caught.cause, { reason: 'base64', type: 'DeserializeInputInvalid' })
    })

    for (const offset of [0, 3]) {
      it(`round-trips buffers and rejects malformed text (decoded offset ${offset})`, async () => {
        const api = await loadWithNativeBase64(offset)
        const bytes = new Uint8Array([0, 1, 2, 250, 251, 252, 253])
        const roundTrip = (value: unknown) =>
          api.deserialize(JSON.parse(JSON.stringify(api.serialize(value))), {
            maxBytes: Infinity,
          })
        const copy = roundTrip(bytes.buffer) as ArrayBuffer
        assert.deepEqual(new Uint8Array(copy), bytes)
        assert.equal(copy.byteLength, bytes.length)
        const empty = roundTrip(new ArrayBuffer(0)) as ArrayBuffer
        assert.equal(empty.byteLength, 0)
        const wire = JSON.stringify(api.serialize(new Uint8Array([1, 2, 3]).buffer))
        for (const [tampered, reason] of [
          ['AQ D', 'base64 size'],
          ['AQI*', 'base64'],
        ]) {
          const caught = thrown(() =>
            api.deserialize(JSON.parse(wire.replace('AQID', tampered)), { maxBytes: Infinity }),
          )
          // The native SyntaxError must not escape: the public error carries the reason.
          assert.ok(api.isReconcileError(caught))
          assert.deepEqual(caught.cause, { reason, type: 'DeserializeInputInvalid' })
          const measured = thrown(() =>
            api.requiredMaxBytes(JSON.parse(wire.replace('AQID', tampered)), {
              maxBytes: Infinity,
            }),
          )
          assert.ok(api.isReconcileError(measured))
          assert.deepEqual(measured.cause, caught.cause)
        }
        assert.equal(api.requiredMaxBytes(JSON.parse(wire), { maxBytes: Infinity }), 8 * 3)
      })
    }
  })
})

it('round-trips long and short buffers with a view in one document', () => {
  const big = new ArrayBuffer(400)
  new Uint8Array(big).forEach((_, index, array) => (array[index] = index % 251))
  const small = new Uint8Array([9, 8, 7]).buffer
  const copy = decodeText(encodeText({ big, small, view: new Uint8Array(big, 10, 20) })) as {
    big: ArrayBuffer
    small: ArrayBuffer
    view: Uint8Array
  }
  assert.deepEqual(new Uint8Array(copy.big), new Uint8Array(big))
  assert.deepEqual(new Uint8Array(copy.small), new Uint8Array(small))
  assert.equal(copy.view.buffer, copy.big)
  assert.equal(copy.view.byteOffset, 10)
  assert.equal(copy.view.length, 20)
})

it('keeps shapes apart that share a prefix or diverge inside a key', () => {
  const records = [
    { alpha: 1, beta: 2 },
    { alpha: 1, bravo: 2 },
    { alpha: 1 },
    { alpha: 1, beta: 2, gamma: 3 },
    { al: 1 },
    { 0: 'a', 1: 'b' },
    { 0: 'a', 2: 'c' },
  ]
  const copy = decodeText(encodeText(records)) as typeof records
  assert.deepEqual(copy, records)
  for (const [index, record] of records.entries())
    assert.deepEqual(Object.keys(copy[index]), Object.keys(record))
})

it('rejects symbol-keyed properties', () => {
  assert.deepEqual(
    failure(() => encodeText({ [Symbol('key')]: 1 })),
    { reason: 'symbol key', type: 'SerializeValueUnsupported' },
  )
})
